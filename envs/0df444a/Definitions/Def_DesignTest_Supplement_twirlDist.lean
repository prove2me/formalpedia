-- Prove2me | Definitions.Def_DesignTest_Supplement_twirlDist
-- name    : DesignTest_Supplement_twirlDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:03:06.719253+00:00
-- url     : https://prove2.me/theorems/de166d36-6c6a-40da-b1b1-faeb6c2a847b
-- title:
--   Twirling channel, $t$-twirling diamond distance $\mathrm{Dist}^{(t)}_\diamond$, unitary frame potential $F_t$, oracles $U^{\pm1}$ and $C_U$
-- statement:
--   Let $\nu$ be a probability measure on $U(d)$ and $t\ge1$.
--
--   1. The **$t$-fold twirling channel** is $G^{(t)}_\nu(X)=\mathbb E_{U\sim\nu}[U^{\otimes t}XU^{\dagger\otimes t}]$ on $(\mathbb C^d)^{\otimes t}$.
--   2. The **diamond norm** of a linear map $T$ is $\|T\|_\diamond=\max_{\|X\|_1=1}\|(T\otimes\mathrm{id})(X)\|_1$, the identity acting on a reference of the same dimension $d^t$; the **$t$-twirling diamond distance** is
--
--   $$\mathrm{Dist}^{(t)}_\diamond(\mu,\nu)=\tfrac12\big\|G^{(t)}_\mu-G^{(t)}_\nu\big\|_\diamond .$$
--
--   3. The **unitary frame potential** is $F_t(\nu)=\|M_t(\nu)\|_2^2$ with $M_t(\nu)=\mathbb E_{U\sim\nu}[U^{\otimes t}\otimes\bar U^{\otimes t}]$.
--   4. A query applies $U^{\sigma}$, $\sigma\in\{+1,-1\}$, $U^{-1}=U^\dagger$; the **controlled oracle** is $C_U=\sum_{i=0}^m|i\rangle\langle i|\otimes U_i$ with $U_0=I$.
--   5. Two matrices **agree up to phase** if $A=e^{i\theta}B$; a finite list is **one phase representative per element** of a phase-closed set of unitaries.
--
--   These objects define unitary design testing (Problem 5.2), frame-potential estimation (Problem 6.1), the access models of Definitions 3.7–3.8 and the support lists of §5.3.
--
--   **Formalization Note.** Expectations are entrywise Bochner integrals of bounded continuous functions; $\|\cdot\|_1$ is the published `DistQuantumQuery.traceNorm`; $M_t(\nu)$ is the published `momentOp`; the maximum in the diamond norm is a real `sSup` over all complex matrices of trace norm one, a nonempty bounded set for probability measures.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), §3.1, p.14 (diamond norm); Definition 3.11, eq. (7), p.17; Definition 3.13, eq. (9), p.18; Definitions 3.7–3.8, pp.15–16; eq. (75), p.44; §5.3, pp.60–62

import Mathlib
import Definitions.Def_RandomGateDesign_MasterBound_Moments
import Definitions.Def_DistQuantumQuery_traceNorm

set_option autoImplicit false

namespace DesignTest.Supplement

open MeasureTheory RandomGateDesign.MasterBound
open scoped Kronecker Matrix

/-- `A^{⊗t}` on `(ℂ^d)^{⊗t}`, indexed by words `x : Fin t → Fin d`: entry `∏_k A_{x_k y_k}`. -/
def tensorU {d : ℕ} (t : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin t → Fin d) (Fin t → Fin d) ℂ :=
  Matrix.of fun x y => ∏ k, A (x k) (y k)

/-- The extension `(G^{(t)}_ν ⊗ id_n)(X) = E_{U∼ν}[(U^{⊗t} ⊗ I_n) X (U^{⊗t} ⊗ I_n)†]` of the `t`-fold
**twirling channel** `G^{(t)}_ν(X) := E_{U∼ν}[U^{⊗t} X U^{†⊗t}]` (A. Kawachi, Y. Nakata, Y. Takeuchi,
*Testing State and Unitary Designs*, STOC 2027 submission (sha256 e2f0a429…), Definition 3.11, eq. (7),
p.17) by the identity on a reference system indexed by `n`.

**Formalization Note.** The expectation is entrywise (Bochner integral of each entry; every entry is a
bounded continuous function of `U`). The system comes first, the reference second. -/
noncomputable def twirlExt {d : ℕ} (ν : Measure (U d)) (t : ℕ) {n : Type} [Fintype n] [DecidableEq n]
    (X : Matrix ((Fin t → Fin d) × n) ((Fin t → Fin d) × n) ℂ) :
    Matrix ((Fin t → Fin d) × n) ((Fin t → Fin d) × n) ℂ :=
  Matrix.of fun a b => ∫ g, ((tensorU t (g : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (1 : Matrix n n ℂ)) * X *
      (tensorU t (g : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (1 : Matrix n n ℂ))ᴴ) a b ∂ν

/-- **The `t`-twirling diamond distance** `Dist⋄^{(t)}(μ, ν) := ½ ‖G^{(t)}_μ − G^{(t)}_ν‖⋄` (STOC 2027
submission (sha256 e2f0a429…), eq. (75), p.44), with the diamond norm
`‖T‖⋄ := max_{‖X‖₁ = 1} ‖(T ⊗ id)(X)‖₁`, the identity acting on a reference system of the same dimension
`d^t` as the input of `T` (p.14).

**Formalization Note.** `X` ranges over all complex matrices of trace norm one on system ⊗ reference
(`DistQuantumQuery.traceNorm`, the sum of singular values); the maximum is the real supremum `sSup`.
For probability measures the set is nonempty and bounded by `2`, so `sSup` is not a junk value. -/
noncomputable def twirlDist {d : ℕ} (t : ℕ) (μ ν : Measure (U d)) : ℝ :=
  sSup {r : ℝ | ∃ X : Matrix ((Fin t → Fin d) × (Fin t → Fin d)) ((Fin t → Fin d) × (Fin t → Fin d)) ℂ,
      DistQuantumQuery.traceNorm X = 1 ∧
      r = DistQuantumQuery.traceNorm (twirlExt μ t X - twirlExt ν t X)} / 2

/-- **The `t`-th unitary frame potential** `F_t(ν) := ‖M_t(ν)‖₂² = Σ_{p,q} |M_t(ν)_{pq}|²` with
`M_t(ν) = E_{U∼ν}[U^{⊗t} ⊗ Ū^{⊗t}]` (STOC 2027 submission (sha256 e2f0a429…), Definition 3.13, eq. (9),
p.18; eq. (7), p.17).

**Formalization Note.** `M_t(ν)` is the published `RandomGateDesign.MasterBound.momentOp ν t`. The
identity `F_t(ν) = E_{U,V∼ν}|Tr(U†V)|^{2t}` of (9) is not part of the definition. -/
noncomputable def unitaryFP {d : ℕ} (ν : Measure (U d)) (t : ℕ) : ℝ :=
  ∑ p, ∑ q, ‖momentOp ν t p q‖ ^ 2

/-- One query direction: `none` = no query (identity), `some true` = `A`, `some false` = `A† = A⁻¹`
(STOC 2027 submission (sha256 e2f0a429…), p.15: `U_i^{σ}`, `σ ∈ {+1, −1}`, `U_i^{−1} = U_i†`). -/
def uPow {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : Option Bool → Matrix ι ι ℂ
  | none => 1
  | some true => A
  | some false => Aᴴ

/-- **The controlled oracle** `C_U := Σ_{i=0}^{m} |i⟩⟨i| ⊗ U_i` with `U_0 := I` (STOC 2027 submission
(sha256 e2f0a429…), Definition 3.8, p.16), on the index register `Fin (m+1)` tensored with `ℂ^d`.
Index `0` is the identity, index `i + 1` the `i`-th sample (`Fin m`, from `0`). The global phase of each
`U_i` is part of the oracle. -/
def ctrlU {d m : ℕ} (u : Fin m → U d) :
    Matrix (Fin (m + 1) × Fin d) (Fin (m + 1) × Fin d) ℂ :=
  Matrix.of fun a b =>
    if a.1 = b.1 then
      (Fin.cons (1 : Matrix (Fin d) (Fin d) ℂ) (fun i => (u i : Matrix (Fin d) (Fin d) ℂ)) :
        Fin (m + 1) → Matrix (Fin d) (Fin d) ℂ) a.1 a.2 b.2
    else 0

/-- Two matrices **agree up to global phase**: `A = e^{iθ} B` for some real `θ` (STOC 2027 submission
(sha256 e2f0a429…), §5.3, pp.59–62). -/
def PhaseEq {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ θ : ℝ, A = Complex.exp ((θ : ℂ) * Complex.I) • B

/-- `R` is **one phase representative per element** of a phase-closed set `S` of unitaries (STOC 2027
submission (sha256 e2f0a429…), p.60: "After fixing one phase representative for each element"; p.62:
"Fix these phases"): `R ⊆ S`, every element of `S` agrees with some element of `R` up to phase, and no
two distinct elements of `R` agree up to phase. -/
def IsPhaseReps {d : ℕ} (R : Finset (U d)) (S : Set (U d)) : Prop :=
  (∀ V ∈ R, V ∈ S) ∧
    (∀ V ∈ S, ∃ W ∈ R, PhaseEq (V : Matrix (Fin d) (Fin d) ℂ) (W : Matrix (Fin d) (Fin d) ℂ)) ∧
    (∀ V ∈ R, ∀ W ∈ R,
      PhaseEq (V : Matrix (Fin d) (Fin d) ℂ) (W : Matrix (Fin d) (Fin d) ℂ) → V = W)

end DesignTest.Supplement


