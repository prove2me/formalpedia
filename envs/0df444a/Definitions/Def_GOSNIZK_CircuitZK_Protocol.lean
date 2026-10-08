-- Prove2me | Definitions.Def_GOSNIZK_CircuitZK_Protocol
-- name    : GOSNIZK_CircuitZK_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:39.249918+00:00
-- url     : https://prove2.me/theorems/babd77e0-5b7b-482c-b68f-95cef44e36cb
-- title:
--   The Circuit SAT prover of Figure 3 and the simulator $S_2$ of the proof of Lemma 8 (pp. 14–15)
-- statement:
--   Fix a homomorphic proof commitment scheme and a key $ck$. On a circuit $C$ with $n$ wires, the prover and the simulator use the same coins: a randomizer $r_i \in R$ per wire and fresh randomness in $R_{\mathrm{proof}}$ for each 0/1 proof, all uniform and independent. Put $r'_{\mathrm{out}} = 0$ and $r'_i = r_i$ for the other wires.
--
--   **The prover** $P(ck, C, w)$ of Figure 3, with $b_i \in \{0, 1\}$ the value of wire $i$:
--   1. commits $c_i = \mathrm{com}(b_i; r_i)$ for every wire other than the output wire, and $c_{\mathrm{out}} = \mathrm{com}(1; 0)$;
--   2. for every wire, makes a 0/1 proof $\pi_i = P_{01}(ck, b_i, r'_i)$;
--   3. for every NAND gate $(i, j, k)$, makes a 0/1 proof
--   $$\pi_{ijk} = P_{01}(ck,\ b_i + b_j + 2b_k - 2,\ r'_i + r'_j + 2r'_k)$$
--   for the gate commitment $c_i c_j c_k^2\,\mathrm{com}(-2; 0)$.
--
--   **The simulator** $S_2(ck, tk, C)$ never sees a witness. With $m_{\mathrm{out}} = 1$ and $m_i = 0$ for every other wire, it
--   1. commits $c_i = \mathrm{com}(m_i; r'_i)$, that is $c_{\mathrm{out}} = \mathrm{com}(1; 0)$ and $c_i = \mathrm{com}(0; r_i)$ otherwise;
--   2. makes $\pi_i = P_{01}(ck, m_i, r'_i)$ for every wire;
--   3. for every gate $(i, j, k)$, uses the trapdoor to open the gate commitment, whose known opening is $(\mu, s) = (m_i + m_j + 2m_k - 2,\ r'_i + r'_j + 2r'_k)$, to the message $0$: $s' = \mathrm{Topen}_{tk}(\mu, s, 0)$, and makes $\pi_{ijk} = P_{01}(ck, 0, s')$.
--
--   A proof is the list of wire commitments, the list of wire proofs and the list of gate proofs. $P$ and $S_2$ denote the laws of these lists when the coins are uniform.
--
--   **Formalization Note** The paper's simulator opens only the gate's output commitment, $r'_k = \mathrm{Topen}_{tk}(0, r_k, 1)$, and uses the opening $(0, r_i + r_j + 2r'_k)$ of the gate commitment. That recipe fails when the output wire is an input of a gate (the gate message is then $1$ or $2$, and $2$ has no 0/1 opening). The simulator here trapdoor-opens the whole gate commitment to $0$ instead, which works for every gate and uses only the key, the trapdoor and the circuit. The verifier of Figure 3 is not needed for zero-knowledge and is not defined.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 14, Figure 3 (prover); p. 15, proof of Lemma 8 (simulator S2)

import Mathlib
import Definitions.Def_GOSNIZK_CircuitZK_Scheme
import Definitions.Def_GOSNIZK_CircuitZK_Circuit

namespace GOSNIZK.CircuitZK

/-- A proof of Figure 3 (Groth, Ostrovsky, Sahai, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 14):
one commitment per wire (`coms`, in wire order), one 0/1 proof per wire (`wireProofs`, in wire order) and one 0/1
proof per NAND gate (`gateProofs`, in gate order). -/
structure Proof (C Pf : Type) where
  coms : List C
  wireProofs : List Pf
  gateProofs : List Pf

/-- The coins of the prover of Figure 3 (and of the simulator `S₂`) on a circuit with `n` wires: a randomizer
`r_i ∈ R` per wire, the randomness `ρ_i ∈ R_proof` of each wire's 0/1 proof, and the randomness of each gate's 0/1
proof. -/
abbrev Coins (R Rp : Type) {n : ℕ} (Γ : Circuit n) : Type :=
  (Fin n → R) × (Fin n → Rp) × (Fin Γ.gates.length → Rp)

/-- The randomizers actually used for the wires: `r_out = 0` (Figure 3, step 2), `r_i` otherwise. -/
def wireRand {R : Type} [Zero R] {n : ℕ} (Γ : Circuit n) (r : Fin n → R) : Fin n → R :=
  fun i => if i = Γ.out then 0 else r i

variable {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]

/-- The prover of Figure 3 (p. 14) run on fixed coins: with `r' = wireRand Γ r` and `b_i = w_i` read in `ZMod N`,
1. `c_i = com(b_i; r_i)` for every wire other than the output wire, and `c_out = com(1; 0)`;
2. `π_i = P01(ck, b_i, r'_i; ρ_i)` for every wire;
3. for the `g`-th NAND gate `(i, j, k)`, `π_g = P01(ck, b_i + b_j + 2b_k − 2, r'_i + r'_j + 2r'_k; ρ_g)`. -/
def proveWith (S : Scheme N R C CK XK TK Rp Pf) (ck : CK) {n : ℕ} (Γ : Circuit n) (w : Fin n → Bool)
    (κ : Coins R Rp Γ) : Proof C Pf :=
  let r' := wireRand Γ κ.1
  let b : Fin n → ZMod N := fun i => bit (w i)
  { coms := List.ofFn fun i => if i = Γ.out then S.com ck 1 0 else S.com ck (b i) (r' i)
    wireProofs := List.ofFn fun i => S.P01 ck (b i) (r' i) (κ.2.1 i)
    gateProofs := List.ofFn fun g : Fin Γ.gates.length =>
      let x := Γ.gates.get g
      S.P01 ck (b x.1 + b x.2.1 + 2 * b x.2.2 - 2) (r' x.1 + r' x.2.1 + 2 • r' x.2.2) (κ.2.2 g) }

/-- The prover `P(σ, C, w)` of Figure 3 with `σ = ck`: `proveWith` on uniformly random coins. -/
noncomputable def prove [Fintype R] [Nonempty R] [Fintype Rp] [Nonempty Rp]
    (S : Scheme N R C CK XK TK Rp Pf) (ck : CK) {n : ℕ} (Γ : Circuit n) (w : Fin n → Bool) :
    PMF (Proof C Pf) :=
  (PMF.uniformOfFintype (Coins R Rp Γ)).map (proveWith S ck Γ w)

/-- The simulator `S₂(σ, τ, C)` of the proof of Lemma 8 (p. 15) run on fixed coins, with `σ = ck`, `τ = tk`. It
never sees a witness. With `r' = wireRand Γ r` and `m_i = 1` on the output wire, `m_i = 0` on every other wire:
1. `c_i = com(m_i; r'_i)`, i.e. `c_out = com(1; 0)` and `c_i = com(0; r_i)` otherwise;
2. `π_i = P01(ck, m_i, r'_i; ρ_i)` for every wire;
3. for the `g`-th NAND gate `(i, j, k)`, the gate commitment `c_i c_j c_k² com(−2; 0)` has the opening
   `(μ, s) = (m_i + m_j + 2m_k − 2, r'_i + r'_j + 2r'_k)`; the simulator trapdoor opens it to `0`,
   `s' = Topen_tk(μ, s, 0)`, and sets `π_g = P01(ck, 0, s'; ρ_g)`. -/
def simulateWith (S : Scheme N R C CK XK TK Rp Pf) (ck : CK) (tk : TK) {n : ℕ} (Γ : Circuit n)
    (κ : Coins R Rp Γ) : Proof C Pf :=
  let r' := wireRand Γ κ.1
  let m : Fin n → ZMod N := fun i => if i = Γ.out then 1 else 0
  { coms := List.ofFn fun i => S.com ck (m i) (r' i)
    wireProofs := List.ofFn fun i => S.P01 ck (m i) (r' i) (κ.2.1 i)
    gateProofs := List.ofFn fun g : Fin Γ.gates.length =>
      let x := Γ.gates.get g
      S.P01 ck 0
        (S.Topen tk (m x.1 + m x.2.1 + 2 * m x.2.2 - 2) (r' x.1 + r' x.2.1 + 2 • r' x.2.2) 0) (κ.2.2 g) }

/-- The simulator `S₂(σ, τ, C)`: `simulateWith` on uniformly random coins. -/
noncomputable def simulate [Fintype R] [Nonempty R] [Fintype Rp] [Nonempty Rp]
    (S : Scheme N R C CK XK TK Rp Pf) (ck : CK) (tk : TK) {n : ℕ} (Γ : Circuit n) : PMF (Proof C Pf) :=
  (PMF.uniformOfFintype (Coins R Rp Γ)).map (simulateWith S ck tk Γ)

end GOSNIZK.CircuitZK


