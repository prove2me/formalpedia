-- Prove2me | Definitions.Def_QuantumPRC_ChScheme
-- name    : QuantumPRC_ChScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:06.46731+00:00
-- url     : https://prove2.me/theorems/6a1ca551-821f-4d31-b1b7-0a1c97e44dcf
-- title:
--   Secret-key codes from $n_{\mathrm L}$ to $n_{\mathrm P}$ qubits; robustness (43), Haar pseudorandomness (44), PRIC (Definition 4.4)
-- statement:
--   A **channel-level secret-key code** from $n_{\mathrm L}$ logical to $n_{\mathrm P}$ physical qubits consists of a key generator $\mathsf{KeyGen}(1^\lambda,1^W;r)$ reading a uniformly random coin string $r$ of length $k(\lambda)$, and, for each key $\mathsf{sk}$, channels $\mathrm{Enc}_{\mathsf{sk}}$ (from $n_{\mathrm L}(\lambda)$ to $n_{\mathrm P}(\lambda)$ qubits) and $\mathrm{Dec}_{\mathsf{sk}}$ (back). $W$ is a parameter given in unary.
--
--   1. **Robustness (43)** for a noise family $\mathcal E=\{\mathcal E_\lambda\}$ at parameters $W(\lambda)$: $\big\|\mathbb E_{\mathsf{sk}\leftarrow\mathsf{KeyGen}}(\mathrm{Dec}_{\mathsf{sk}}\circ\mathcal E_\lambda\circ\mathrm{Enc}_{\mathsf{sk}})-\mathrm{id}\big\|_\diamond\le\mathsf{negl}(\lambda)$.
--   2. **Pseudorandomness (44)** with the Haar ideal: for every uniform QPT adversary $\mathcal A$ with one oracle,
--   $$
--   \Big|\Pr_{\mathsf{sk}\leftarrow\mathsf{KeyGen}(1^\lambda)}\big[1\leftarrow\mathcal A^{\mathrm{Enc}_{\mathsf{sk}}}\big]-\Pr_{V\leftarrow\mu_{n_{\mathrm L}\to n_{\mathrm P}}}\big[1\leftarrow\mathcal A^{V(\cdot)V^\dagger}\big]\Big|\le\mathsf{negl}(\lambda),
--   $$
--   where the ideal channel is sampled independently of the key and reused for all queries.
--   3. **PRIC robust to every $w$-local noise** (Definition 4.4): with $W(\lambda)=\min(w(\lambda),n_{\mathrm P}(\lambda))$, robustness holds for every $w$-local noise family (Definition 3.7) and pseudorandomness holds.
--   4. **Implementability**: $\mathsf{KeyGen}$ is PPT (a polynomial-time function of $1^\lambda$, $1^W$ and polynomially many coins, outputting a classical key code), and $\mathrm{Enc}$, $\mathrm{Dec}$ are uniform QPT: one polynomial-time machine prints, from $(1^\lambda,1^W,\mathsf{sk})$, a circuit whose channel is exactly $\mathrm{Enc}_{\mathsf{sk}}$ (respectively $\mathrm{Dec}_{\mathsf{sk}}$).
--
--   **Formalization Note** The Haar-random isometry is $V=U\iota$ with $\iota|x\rangle=|x\rangle|0^{n_{\mathrm P}-n_{\mathrm L}}\rangle$ and $U$ distributed by the published `QAlgorithms.Schur.unitaryHaar` on $U(2^{n_{\mathrm P}})$, as on p.69 of the paper; the integrand is a polynomial in the entries of $U$ and $\bar U$, so the integral is the true expectation. The parameter $W$ is capped at $n_{\mathrm P}$, so the scheme's input stays polynomial in $\lambda$ for every $w$. Robustness is required separately for each noise family, and noise families are independent of the key.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Definition 4.3, p.25 (syntax, (43), (44)); Definition 4.4, p.26; §3.1, p.16 and p.69 (Haar isometries)

import Mathlib
import Definitions.Def_QuantumPRC_IsLocalNoise
import Definitions.Def_QuantumPRC_Assumption5
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles

open Matrix MeasureTheory

namespace QuantumPRC

/-- The bijection `{0,1}^n ≃ Fin (2^n)` used to index `2^n × 2^n` matrices by bit strings. -/
def bitsEquiv (n : ℕ) : Bits n ≃ Fin (2 ^ n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- `|x⟩ ↦ |x⟩|0^{nP−nL}⟩`: the first `nL` bits are `x`, the rest are `0`. -/
def padZero (nL nP : ℕ) (x : Bits nL) : Bits nP :=
  fun i => if h : i.val < nL then x ⟨i.val, h⟩ else false

/-- The isometry `V = U · ι` from `nL` to `nP` qubits given by a unitary `U` on `nP` qubits, where
`ι|x⟩ = |x⟩|0^{nP−nL}⟩`. For `U` Haar-random on `U(2^{nP})` this is the Haar-random isometry
`µ_{nL→nP}` (arXiv:2609.38986, p.16 and p.69: "`V|ψ⟩ := U(|ψ⟩ ⊗ |0^{m−n}⟩)` with `U` Haar-random"). -/
def haarIsoMat (nL nP : ℕ) (U : Matrix.unitaryGroup (Fin (2 ^ nP)) ℂ) :
    Matrix (Bits nP) (Bits nL) ℂ :=
  fun y x => (U : Matrix (Fin (2 ^ nP)) (Fin (2 ^ nP)) ℂ) (bitsEquiv nP y) (bitsEquiv nP (padZero nL nP x))

/-- **Channel-level secret-key code from `nL` to `nP` qubits, with a parameter `W`.**
Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), Definition 4.3 (syntax), p.25: KeyGen outputs a
classical key `sk`; `Enc_sk` is a CPTP map from `nL` logical to `nP` physical qubits; `Dec_sk` is a CPTP
map back.

`Key λ W` is the key space; `keyGen λ W r` is the key produced from a uniformly random coin string
`r ∈ {0,1}^{kc(λ)}`; `enc λ W sk` and `dec λ W sk` are the channels. All three also read a parameter
`W` (a natural number given in unary, see `IsPRICAt`).

**Formalization Note.** Efficiency (KeyGen PPT, Enc and Dec uniform QPT) is the separate predicate
`ChScheme.Implementable`. -/
structure ChScheme (nL nP : ℕ → ℕ) where
  Key : ℕ → ℕ → Type
  kc : ℕ → ℕ
  keyGen : ∀ lam W, Bits (kc lam) → Key lam W
  enc : ∀ lam W, Key lam W → Superop (Bits (nL lam)) (Bits (nP lam))
  dec : ∀ lam W, Key lam W → Superop (Bits (nP lam)) (Bits (nL lam))

namespace ChScheme

variable {nL nP : ℕ → ℕ} (S : ChScheme nL nP)

/-- `𝔼_{sk←KeyGen(1^λ)} (Dec_sk ∘ N ∘ Enc_sk)` at parameter `W`, for a channel `N` on `nP(λ)` qubits. -/
noncomputable def avgDecNEnc (lam W : ℕ) (N : Superop (Bits (nP lam)) (Bits (nP lam))) :
    Superop (Bits (nL lam)) (Bits (nL lam)) :=
  fun ρ => ((2 : ℂ) ^ S.kc lam)⁻¹ •
    ∑ r : Bits (S.kc lam), S.dec lam W (S.keyGen lam W r) (N (S.enc lam W (S.keyGen lam W r) ρ))

/-- **Robustness (43)**, Definition 4.3, p.25: `‖𝔼_{sk←KeyGen(1^λ)}(Dec_sk ∘ E_λ ∘ Enc_sk) − id‖⋄ ≤ negl(λ)`,
for the noise family `E` and the parameter sequence `W`. -/
def Robust (W : ℕ → ℕ) (E : ∀ lam, WildeQIT.QChannel (Bits (nP lam)) (Bits (nP lam))) : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
    diamondDist (S.avgDecNEnc lam (W lam) (E lam).apply) id ≤ ν lam

/-- **Pseudorandomness (44) with the Haar ideal distribution**, Definitions 4.3–4.4, pp.25–26:
for any QPT adversary `A^{(·)}`, `|Pr_{sk←KeyGen(1^λ)}[1 ← A^{Enc_sk}(1^λ)] −
Pr_{sk←KeyGen(1^λ), I←D_λ}[1 ← A^I(1^λ)]| ≤ negl(λ)`, with `D_λ = µ_{nL(λ)→nP(λ)}`: "the ideal channel is
sampled independently of the key and reused for all oracle queries" (p.25).

**Formalization Note.** Adversaries are uniform families of oracle circuits with one oracle from
`nL(λ)` to `nP(λ)` qubits (adaptive, possibly entangled with the adversary's other wires). The ideal
oracle is `V(·)V†` with `V = U·ι`, `U` Haar on `U(2^{nP})` (`QAlgorithms.Schur.unitaryHaar`). The
integrand is a polynomial in the entries of `U` and `Ū`, hence continuous and bounded on the compact
group, so the Bochner integral is the true expectation. -/
def Pseudorandom (W : ℕ → ℕ) : Prop :=
  ∀ A : ∀ lam, OCirc (nL lam) (nP lam) 1, IsUniformAdv A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |avg (fun r : Bits (S.kc lam) =>
          (A lam).accept (fun _ => S.enc lam (W lam) (S.keyGen lam (W lam) r)) []) -
        ∫ U, (A lam).accept (fun _ => conjMap (haarIsoMat (nL lam) (nP lam) U)) []
          ∂(QAlgorithms.Schur.unitaryHaar (2 ^ nP lam))| ≤ ν lam

/-- The capped parameter `W(λ) = min(w(λ), nP(λ))`: the scheme receives `1^{W(λ)}`, so its input is
polynomial in `λ` whatever `w` is. -/
def capW (w nP : ℕ → ℕ) : ℕ → ℕ := fun lam => min (w lam) (nP lam)

/-- **PRIC robust to every `w`-local noise**, Definition 4.4, p.26: "We call a tuple of algorithms
`(KeyGen, Enc, Dec)` a pseudorandom isometric code (PRIC) robust to `E` if it is a secret-key
`µ_{nL→nP}`-QPRC robust to `E`", for every `w`-local noise family `E` (Definition 3.7), with the
scheme run at the parameter `W = min(w, nP)`.

**Formalization Note.** Robustness is required for each noise family separately (`∃ negl` after the
family), and noise families are arbitrary and independent of the key, as in Definition 4.3. -/
def IsPRICAt (w : ℕ → ℕ) : Prop :=
  (∀ E : ∀ lam, WildeQIT.QChannel (Bits (nP lam)) (Bits (nP lam)),
      IsLocalNoise w nP E → S.Robust (capW w nP) E) ∧
    S.Pseudorandom (capW w nP)

/-- **Implementability** (syntax of Definition 4.3, p.25): KeyGen is a PPT algorithm (here: a
polynomial-time function of `1^λ`, `1^W` and polynomially many fair coins, outputting a classical key
code), and Enc and Dec are uniform QPT algorithms: one polynomial-time machine prints, from
`(1^λ, 1^W, sk)`, a circuit whose channel is exactly `Enc_sk` (respectively `Dec_sk`).

**Formalization Note.** A PPT KeyGen is a special case of the printed QPT KeyGen. -/
def Implementable : Prop :=
  PolyBounded S.kc ∧
  ∃ (code : ∀ lam W, S.Key lam W → List Bool)
    (encC : ∀ lam W, S.Key lam W → Circuit (nL lam) (nP lam))
    (decC : ∀ lam W, S.Key lam W → Circuit (nP lam) (nL lam)),
    (∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ lam W r, f (tupleCode [unary lam, unary W, bits r]) = code lam W (S.keyGen lam W r)) ∧
    (∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ lam W k, f (tupleCode [unary lam, unary W, code lam W k]) = (encC lam W k).encode) ∧
    (∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
      ∀ lam W k, f (tupleCode [unary lam, unary W, code lam W k]) = (decC lam W k).encode) ∧
    (∀ lam W k, (encC lam W k).channel = S.enc lam W k) ∧
    (∀ lam W k, (decC lam W k).channel = S.dec lam W k)

end ChScheme

end QuantumPRC


