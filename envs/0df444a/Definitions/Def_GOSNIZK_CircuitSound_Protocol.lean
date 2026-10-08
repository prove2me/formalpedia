-- Prove2me | Definitions.Def_GOSNIZK_CircuitSound_Protocol
-- name    : GOSNIZK_CircuitSound_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:28.939451+00:00
-- url     : https://prove2.me/theorems/48ed9511-403e-4eb0-909e-f4df7a8c9c44
-- title:
--   The Circuit SAT proof of Figure 3: prover, verifier, extractor, perfect completeness, soundness and knowledge extraction (pp. 5, 14–15)
-- statement:
--   Fix a homomorphic proof commitment scheme. The protocol of Figure 3 uses a commitment key as common reference string: $(ck,xk)\leftarrow K_{\mathrm{binding}}$ and $\sigma=ck$.
--
--   **Proof.** A proof for a circuit $C$ on $n$ wires consists of a commitment $c_i\in\mathcal C$ and a 0/1 proof $\pi_i$ for every wire $i$, and a 0/1 proof $\pi_{ijk}$ for every gate $(i,j,k)$.
--
--   **Prover.** On input $(\sigma,C,w)$ with $C(w)=1$, and coins $r_i\in\mathcal R$ and proof randomness for each 0/1 proof:
--   1. $c_i=\mathrm{com}(w_i;r_i)$ for every wire $i\ne\mathrm{out}$, and $c_{\mathrm{out}}=\mathrm{com}(1;0)$, i.e. $r_{\mathrm{out}}=0$;
--   2. $\pi_i=P_{01}(ck,w_i,r_i)$ for every wire;
--   3. for every gate $(i,j,k)$, $\pi_{ijk}=P_{01}(ck,\ w_i+w_j+2w_k-2,\ r_i+r_j+2r_k)$, a proof that $c_ic_jc_k^2\,\mathrm{com}(-2;0)$ contains $0$ or $1$.
--
--   **Verifier.** On input $(\sigma,C,\pi)$ it accepts iff $c_{\mathrm{out}}=\mathrm{com}(1;0)$, $V_{01}(ck,c_i,\pi_i)=1$ for every wire, and
--   $$V_{01}\big(ck,\ c_ic_jc_k^2\,\mathrm{com}(-2;0),\ \pi_{ijk}\big)=1$$
--   for every gate $(i,j,k)$.
--
--   **Extractor.** $E_1=K_{\mathrm{binding}}$ with extraction key $\xi=xk$, and $E_2(\sigma,\xi,C,\pi)$ returns the wires $w_i=1$ iff $\mathrm{Ext}_{xk}(c_i)=1$.
--
--   The three properties of Section 2 (p. 5) for this protocol are:
--   1. **perfect completeness**: for every key $ck$ output by $K_{\mathrm{binding}}$ or $K_{\mathrm{hiding}}$, every circuit $C$, every $w$ with $C(w)=1$ and every choice of the prover's coins, the verifier accepts the prover's output;
--   2. **perfect soundness**: for every $(ck,xk)$ output by $K_{\mathrm{binding}}$, every circuit $C$ with no satisfying assignment and every purported proof $\pi$, the verifier rejects;
--   3. **perfect knowledge extraction**: for every $(ck,xk)$ output by $K_{\mathrm{binding}}$, every circuit $C$ and every proof $\pi$ the verifier accepts, $C(E_2(\sigma,xk,C,\pi))=1$.
--
--   **Formalization Note** Gates are indexed by their position in the gate list. Bits enter $\mathcal M$ as $0,1$; the prover uses $r_{\mathrm{out}}=0$ in the wire proof of the output and in every gate where the output wire occurs. The verifier is a `Prop`; "all wires have a corresponding commitment" is enforced by the type of a proof. The paper's "for all adversaries, $\Pr[\dots]=1$" (completeness) and "$\Pr[\dots]=0$" (soundness) are stated for every key in the support of the generator and every input or proof an adversary could choose. Completeness is stated on keys of both modes, which covers both Theorem 6 ($K=K_{\mathrm{binding}}$) and the completeness clause of Theorem 11 ($K=K_{\mathrm{hiding}}$). The extractor is the concrete one of the proof of Theorem 6, not "there exists an extractor": an extractor with unlimited computation could search for a witness, which would make knowledge extraction a restatement of soundness. With $E_1=K_{\mathrm{binding}}$, the first equation of perfect knowledge extraction (p. 5) holds by definition.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 5 (Perfect completeness, Perfect soundness, Perfect knowledge extraction); p. 14, Figure 3; p. 15, proof of Theorem 6

import Mathlib
import Definitions.Def_GOSNIZK_CircuitSound_Scheme
import Definitions.Def_GOSNIZK_CircuitSound_Circuit

namespace GOSNIZK.CircuitSound

/-- A proof of the protocol of Figure 3 (Groth, Ostrovsky, Sahai, *New Techniques for
Noninteractive Zero-Knowledge*, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 14) for
the circuit `Γ`: a commitment `c i` and a 0/1 proof `πw i` for every wire `i`, and a 0/1 proof
`πg g` for every gate, gates indexed by their position `g` in `Γ.gates`. -/
structure Proof (C Prf : Type) {n : ℕ} (Γ : Circuit n) where
  c : Fin n → C
  πw : Fin n → Prf
  πg : Fin Γ.gates.length → Prf

namespace Scheme

variable {N : ℕ} {R C CK XK TK Rp Prf : Type} [AddCommGroup R] [CommGroup C]
variable (S : Scheme N R C CK XK TK Rp Prf)

/-- The gate commitment `c_i c_j c_k² com(−2; 0)` of Figure 3. -/
def gateCom (ck : CK) (ci cj ck' : C) : C := ci * cj * ck' ^ 2 * S.com ck (-2) 0

/-- The randomizers the prover uses for the wires: `r_i` for `i ≠ out` and `r_out = 0`. -/
def wireRand {n : ℕ} (Γ : Circuit n) (r : Fin n → R) : Fin n → R :=
  fun i => if i = Γ.out then 0 else r i

/-- The prover of Figure 3 on common reference string `σ = ck`, circuit `Γ` and wires `w`, with
coins `r` (wire randomizers), `ρw` (randomness of the wire proofs) and `ρg` (randomness of the gate
proofs):
1. `c_i = com(w_i; r_i)` for `i ≠ out`, and `c_out = com(1; 0)`;
2. `π_i = P01(ck, w_i, r_i; ρw_i)`, with `r_out = 0`;
3. for a gate `(i, j, k)`, `π_ijk = P01(ck, w_i + w_j + 2w_k − 2, r_i + r_j + 2r_k; ρg_g)`, again with
   `r_out = 0`. -/
def prove (ck : CK) {n : ℕ} (Γ : Circuit n) (w : Fin n → Bool) (r : Fin n → R)
    (ρw : Fin n → Rp) (ρg : Fin Γ.gates.length → Rp) : Proof C Prf Γ where
  c i := if i = Γ.out then S.com ck 1 0 else S.com ck (ofBit (w i)) (r i)
  πw i := S.P01 ck (ofBit (w i)) (wireRand Γ r i) (ρw i)
  πg g :=
    S.P01 ck
      (ofBit (w Γ.gates[g].1) + ofBit (w Γ.gates[g].2.1) + 2 * ofBit (w Γ.gates[g].2.2) - 2)
      (wireRand Γ r Γ.gates[g].1 + wireRand Γ r Γ.gates[g].2.1 + 2 • wireRand Γ r Γ.gates[g].2.2)
      (ρg g)

/-- The verifier of Figure 3 accepts `π` for `Γ` on `σ = ck`: `c_out = com(1; 0)`, every wire
proof is accepted by `V01`, and for every gate `(i, j, k)` the gate proof is accepted by `V01` for
the commitment `c_i c_j c_k² com(−2; 0)`. -/
def Verify (ck : CK) {n : ℕ} (Γ : Circuit n) (π : Proof C Prf Γ) : Prop :=
  π.c Γ.out = S.com ck 1 0 ∧
  (∀ i : Fin n, S.V01 ck (π.c i) (π.πw i) = true) ∧
  (∀ g : Fin Γ.gates.length,
    S.V01 ck (S.gateCom ck (π.c Γ.gates[g].1) (π.c Γ.gates[g].2.1) (π.c Γ.gates[g].2.2))
      (π.πg g) = true)

/-- The knowledge extractor `E₂(σ, ξ, C, π)` of the proof of Theorem 6 (p. 15), with `ξ = xk`:
wire `i` is read as true iff the extracted message `Ext_xk(c_i)` is `1`. -/
def extract (xk : XK) {n : ℕ} {Γ : Circuit n} (π : Proof C Prf Γ) : Fin n → Bool :=
  fun i => decide (S.Ext xk (π.c i) = 1)

/-- **Perfect completeness** (p. 5) of the protocol of Figure 3, on keys of either mode: for every
key `ck` output by `K_binding` or `K_hiding`, every circuit `Γ`, every `w` with `Γ(w) = 1` and every
choice of the prover's coins, the verifier accepts the prover's output. -/
def CircuitPerfectCompleteness : Prop :=
  ∀ ck : CK, S.IsKey ck → ∀ (n : ℕ) (Γ : Circuit n) (w : Fin n → Bool), Γ.Sat w →
    ∀ (r : Fin n → R) (ρw : Fin n → Rp) (ρg : Fin Γ.gates.length → Rp),
      S.Verify ck Γ (S.prove ck Γ w r ρw ρg)

/-- **Perfect soundness** (p. 5) of the protocol of Figure 3: for every key `ck` output by
`K_binding`, every circuit `Γ` with no satisfying `w` and every purported proof `π`, the verifier
rejects. -/
def CircuitPerfectSoundness : Prop :=
  ∀ (ck : CK) (xk : XK), (ck, xk) ∈ S.Kbind.support → ∀ (n : ℕ) (Γ : Circuit n),
    (¬ ∃ w : Fin n → Bool, Γ.Sat w) → ∀ π : Proof C Prf Γ, ¬ S.Verify ck Γ π

/-- **Perfect knowledge extraction** (p. 5) of the protocol of Figure 3 with the extractor
`E₁ = K_binding`, `E₂ = extract`: for every `(ck, xk)` output by `K_binding`, every circuit `Γ`
and every proof `π` the verifier accepts, the extracted wires satisfy `Γ`. -/
def CircuitPerfectKnowledgeExtraction : Prop :=
  ∀ (ck : CK) (xk : XK), (ck, xk) ∈ S.Kbind.support → ∀ (n : ℕ) (Γ : Circuit n)
    (π : Proof C Prf Γ), S.Verify ck Γ π → Γ.Sat (S.extract xk π)

end Scheme

end GOSNIZK.CircuitSound


