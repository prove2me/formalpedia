-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_HodgeTateChains_Statement
-- name    : Formalism_WachLatticeTwists_HodgeTateChains_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:02.659331+00:00
-- url     : https://prove2.me/theorems/36d0bbf1-afa0-4bc3-9a9f-714e30d1070a
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/HodgeTateChains/Statement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
open Polynomial
def n0 (ℓ H0 : ℕ) : ℕ := sInf {n : ℕ | H0 ≤ ℓ ^ n * (ℓ - 1)}
def mOf (ℓ s H0 : ℕ) : ℕ := 2 * s + n0 ℓ H0 + 1
def rI (ℓ m : ℕ) (U : Finset ℤ) (i : ℤ) : ℕ := ∑ u ∈ U.erase i, (m + padicValInt ℓ (u - i))
def cM (ℓ m : ℕ) (U : Finset ℤ) (a b : ℤ) : ℕ := ∑ i ∈ Finset.Ico a b, (2 + max 1 (rI ℓ m U i))
def cLL (ℓ m : ℕ) (U : Finset ℤ) (a b : ℤ) (d : ℕ) : ℕ := padicValNat ℓ d + cM ℓ m U a b
def c0 (ℓ m : ℕ) (U : Finset ℤ) : ℕ := 2 + ∑ u ∈ U, (m + padicValInt ℓ u)
def beta (ℓ s e : ℕ) : ℤ :=
  if e = 0 then -1 else (s : ℤ) - 1 - e - padicValNat ℓ (e - 1).factorial
def ceilE (ℓ e : ℕ) : ℕ := (e + (ℓ - 1) - 1) / (ℓ - 1)
def cPrime (ℓ s e : ℕ) : ℕ := ∑ i ∈ Finset.range e, (1 + s + padicValNat ℓ (e - i))
def aTB (ℓ s e : ℕ) : ℕ := if e = 0 then s else (e + 2) * s + padicValNat ℓ e + ceilE ℓ e
def cTBof (ℓ s e gK c : ℕ) : ℕ :=
  c + (e + 2) * s + padicValNat ℓ e + e / (ℓ - 1) + 1 + (s + padicValNat ℓ (e + 1)) + gK
def cTB (ℓ s m e gK : ℕ) (U : Finset ℤ) : ℕ :=
  cTBof ℓ s e gK (cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s)))
def TorsKilled (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [AddCommGroup A] [Module ℤ_[ℓ] A] (c : ℕ) : Prop :=
  ∀ x : A, (∃ k : ℕ, ((ℓ : ℤ_[ℓ]) ^ k) • x = 0) → ((ℓ : ℤ_[ℓ]) ^ c) • x = 0
def Rpoly (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Polynomial ℤ_[ℓ] :=
  ∏ a ∈ U.erase i, (X - C (((w ^ (i - a) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))
def HTpoly (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Polynomial ℤ_[ℓ] :=
  ∏ a ∈ U, (X - C (((w ^ (i - a) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))
def MinimalExponentAttained : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ H0 : ℕ,
    H0 ≤ ℓ ^ n0 ℓ H0 * (ℓ - 1) ∧ ∀ n < n0 ℓ H0, ℓ ^ n * (ℓ - 1) < H0
def StatCeil : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ e : ℕ,
    (e : ℚ) / ((ℓ : ℚ) - 1) ≤ ceilE ℓ e ∧ (ceilE ℓ e : ℚ) < (e : ℚ) / ((ℓ : ℚ) - 1) + 1 ∧
      ceilE ℓ e ≤ e / (ℓ - 1) + 1
def StatRVal : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (i : ℤ),
      (Rpoly ℓ w U i).eval 1 ≠ 0 ∧ PadicInt.valuation ((Rpoly ℓ w U i).eval 1) = rI ℓ m U i
def StatBinom : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ b k : ℕ, 1 ≤ b → 0 < k → k < ℓ ^ (b - 1) → ℓ ^ 2 ∣ (ℓ ^ b).choose k
def StatFiltPow : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (N : Type) [AddCommGroup N] (F : ℕ → AddSubgroup N) (γ : N →+ N),
    F 0 = ⊤ → (∀ a, F (a + 1) ≤ F a) → (∀ a, ∀ x ∈ F a, γ x - x ∈ F (a + 1)) →
    ∀ b : ℕ, 1 ≤ b → ∀ x : N, ∃ y : N, ∃ z ∈ F (ℓ ^ (b - 1)),
      (⇑γ)^[ℓ ^ b] x - x = (ℓ ^ 2) • y + z
def StatValNN : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (s n i j : ℕ), 1 ≤ s → i + j = ℓ ^ (s + n) →
    (ℓ : ℚ) / ((ℓ : ℚ) - 1) ≤ (i : ℚ) + (j : ℚ) / ((ℓ : ℚ) ^ (s + n - 1) * ((ℓ : ℚ) - 1)) ∧
    1 / ((ℓ : ℚ) - 1) < min 2 ((ℓ : ℚ) / ((ℓ : ℚ) - 1))
def StatLL3 : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (s H0 h d : ℕ) (U : Finset ℤ) (a b : ℤ), 1 ≤ h → H0 ≤ 2 * h →
    (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) → -(h : ℤ) ≤ a → a < b → b ≤ h →
    padicValNat ℓ d + 1 ≤ mOf ℓ s H0 →
    mOf ℓ s H0 ≤ 2 * s + Nat.log ℓ (2 * h) + 2 ∧
    cLL ℓ (mOf ℓ s H0) U a b d ≤
      mOf ℓ s H0 + (b - a).toNat * (3 + U.card * (mOf ℓ s H0 + Nat.log ℓ (2 * h)))
def StatBetaCount : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ s e : ℕ, 1 ≤ e →
    ((e : ℤ) + 1) * ((s : ℤ) - 1) + s + padicValNat ℓ e - s * e - padicValNat ℓ e.factorial - s
      = beta ℓ s e
def StatIBound : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ s e : ℕ, beta ℓ s e + ceilE ℓ e ≤ (s : ℤ) - 1
def StatACount : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ s e : ℕ,
    cPrime ℓ s e = e * (s + 1) + padicValNat ℓ e.factorial ∧
    ((cPrime ℓ s e + 1 + s + ceilE ℓ e : ℕ) : ℤ) + beta ℓ s e = aTB ℓ s e ∧
    aTB ℓ s e ≤ (e + 2) * s + padicValNat ℓ e + e / (ℓ - 1) + 1
def StatCTBTable : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ (s m e gK : ℕ) (U : Finset ℤ),
    cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s)) = (m - s) + cM ℓ m U 0 ((e : ℤ) + 1) ∧
    cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s)) + aTB ℓ s e + (s + padicValNat ℓ (e + 1)) + gK
      ≤ cTB ℓ s m e gK U
def InjectivityOnLayerOfPower : Prop :=
  ∀ (R : Type) [CommRing R] (Xm : Type) [AddCommGroup Xm] [Module R Xm] (g : Xm →ₗ[R] Xm) (k : ℕ)
    (z : R) (α : Xm ≃ₗ[R] Xm),
    (∀ x, (g ^ k) x - x = z • α x) → (∀ x : Xm, z • x = 0 → x = 0) →
    (∀ x, g x = x → x = 0) ∧ ∀ x, ∃ y, z • x = g y - y
def StatOnePlus : Prop :=
  ∀ (R : Type) [CommRing R] (Xm : Type) [AddCommGroup Xm] [Module R Xm] (ϖ : R),
    IsAdicComplete (Ideal.span {ϖ}) Xm → ∀ E : Xm →ₗ[R] Xm,
    Function.Bijective (fun x : Xm => x + ϖ • E x)
def PerturbationOperatorIntegral : Prop :=
  ∀ (R : Type) [CommRing R] (Xm : Type) [AddCommGroup Xm] [Module R Xm] (ϖ z : R),
    IsAdicComplete (Ideal.span {ϖ}) Xm → (∀ x : Xm, z • x = 0 → x = 0) →
    ∀ g S B : Xm →ₗ[R] Xm, (∀ x, g (S x) - S x = z • x) → (∀ x, S (g x - x) = z • x) →
    (∀ x, (g x + (z * ϖ) • B (g x)) = x → x = 0) ∧
    (∀ y, (∃ x, y = (g x + (z * ϖ) • B (g x)) - x) ↔ ∃ x, y = g x - x) ∧
    ∀ x, ∃ y, z • x = (g y + (z * ϖ) • B (g y)) - y
def InverseOperatorFromInjectivity : Prop :=
  ∀ (R : Type) [CommRing R] (Xm : Type) [AddCommGroup Xm] [Module R Xm] (g : Xm →ₗ[R] Xm) (z : R),
    (∀ x, g x = x → x = 0) → (∀ x, ∃ y, z • x = g y - y) →
    ∃ S : Xm →ₗ[R] Xm, (∀ x, g (S x) - S x = z • x) ∧ ∀ x, S (g x - x) = z • x
def InjectivityPassesToCompletion : Prop :=
  ∀ (R : Type) [CommRing R] (Xm : Type) [AddCommGroup Xm] [Module R Xm] (ϖ z : R),
    IsAdicComplete (Ideal.span {ϖ}) Xm → (∀ x : Xm, z • x = 0 → x = 0) →
    ∀ (X0 : Submodule R Xm) (g : Xm →ₗ[R] Xm),
    (∀ (x : Xm) (n : ℕ), ∃ x0 ∈ X0, ∃ x', x = x0 + (ϖ ^ n) • x') →
    (∀ (n : ℕ) (x : Xm), (ϖ ^ n) • x ∈ X0 → ∃ x0 ∈ X0, (ϖ ^ n) • x = (ϖ ^ n) • x0) →
    (∀ x ∈ X0, g x ∈ X0) → (∀ x ∈ X0, g x = x → x = 0) → (∀ x ∈ X0, ∃ y ∈ X0, z • x = g y - y) →
    (∀ x, g x = x → x = 0) ∧ ∀ x, ∃ y, z • x = g y - y
def StatLemmaA : Prop :=
  ∀ (ℓ : ℕ) (Bm : Type) [AddCommGroup Bm] (Am : AddSubgroup Bm) (T : Bm →+ Bm),
    (∀ x : Bm, ℓ • x ∈ Am → x ∈ Am) →
    (∀ x : Bm, (∀ n : ℕ, ∃ a ∈ Am, ∃ b : Bm, x = a + (ℓ ^ n) • b) → x ∈ Am) →
    (∀ a ∈ Am, T a ∈ Am) →
    (∀ x : Bm, (∃ a ∈ Am, ∃ b : Bm, T x = a + ℓ • b) → ∃ a ∈ Am, ∃ b : Bm, x = a + ℓ • b) →
    ∀ x : Bm, T x ∈ Am → x ∈ Am
def StatEigen : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (i : ℤ) (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V),
    (∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) →
    aeval g ((X - 1) * Rpoly ℓ w U i) = 0 →
    ∀ (k : ℕ) (x x' : V), ((ℓ : ℤ_[ℓ]) ^ k) • x = g x' - x' →
      ∃ y : V, ((ℓ : ℤ_[ℓ]) ^ rI ℓ m U i) • x = g y - y
def StatHTpoly : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ),
    HTpoly ℓ w U i ∣ (X - 1) * Rpoly ℓ w U i ∧ (i ∉ U → HTpoly ℓ w U i = Rpoly ℓ w U i)
def StatEigenInj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (m : ℕ), 1 ≤ m → (ℓ = 2 → 2 ≤ m) →
    PadicInt.valuation ((w : ℤ_[ℓ]) - 1) = m →
    ∀ (U : Finset ℤ) (i : ℤ), i ∉ U →
    ∀ (V : Type) [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V),
    (∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) → aeval g (HTpoly ℓ w U i) = 0 →
    ∀ x : V, g x = x → x = 0
def StatDevSum : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H Gr : ℕ → Type) [∀ k, AddCommGroup (H k)] [∀ k, Module ℤ_[ℓ] (H k)]
    [∀ k, AddCommGroup (Gr k)] [∀ k, Module ℤ_[ℓ] (Gr k)]
    (f : ∀ k, Gr k →ₗ[ℤ_[ℓ]] H (k + 1)) (p : ∀ k, H (k + 1) →ₗ[ℤ_[ℓ]] H k) (c : ℕ → ℕ),
    (∀ x : H 0, x = 0) → (∀ k, Function.Exact (f k) (p k)) →
    (∀ k, ∀ x : Gr k, f k x = 0 → ∃ j : ℕ, ((ℓ : ℤ_[ℓ]) ^ j) • x = 0) →
    (∀ k, TorsKilled ℓ (Gr k) (c k)) →
    ∀ n, TorsKilled ℓ (H n) (∑ k ∈ Finset.range n, c k)
def StatKillSum : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (H Gr : ℕ → Type) [∀ k, AddCommGroup (H k)] [∀ k, Module ℤ_[ℓ] (H k)]
    [∀ k, AddCommGroup (Gr k)] [∀ k, Module ℤ_[ℓ] (Gr k)]
    (f : ∀ k, Gr k →ₗ[ℤ_[ℓ]] H (k + 1)) (p : ∀ k, H (k + 1) →ₗ[ℤ_[ℓ]] H k) (c : ℕ → ℕ) (n : ℕ),
    (∀ x : H 0, x = 0) → (∀ k < n, Function.Exact (f k) (p k)) →
    (∀ k < n, ∀ x : Gr k, ((ℓ : ℤ_[ℓ]) ^ c k) • x = 0) →
    ∀ x : H n, ((ℓ : ℤ_[ℓ]) ^ (∑ k ∈ Finset.range n, c k)) • x = 0
def StatCores : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A B : Type) [AddCommGroup A] [Module ℤ_[ℓ] A] [AddCommGroup B]
    [Module ℤ_[ℓ] B] (res : A →ₗ[ℤ_[ℓ]] B) (cor : B →ₗ[ℤ_[ℓ]] A) (d c : ℕ), d ≠ 0 →
    (∀ x, cor (res x) = d • x) → TorsKilled ℓ B c → TorsKilled ℓ A (padicValNat ℓ d + c)
def StatReindex : Prop :=
  ∀ (ℓ m : ℕ) (U : Finset ℤ) (a : ℤ) (n : ℕ),
    cM ℓ m U a (a + n) = ∑ k ∈ Finset.range n, (2 + max 1 (rI ℓ m U (a + k)))
def StatBKSubspace : Prop :=
  ∀ (O F : Type) [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F],
    ¬ IsField O →
    ∀ (HV HV' : Type) [AddCommGroup HV] [Module F HV] [AddCommGroup HV'] [Module F HV']
      (pair : HV →ₗ[F] HV' →ₗ[F] F) (Hf : Submodule F HV) (Hf' : Submodule F HV'),
    (∀ a, a ∈ Hf ↔ ∀ b ∈ Hf', pair a b = 0) →
    ∀ a : HV, (∀ b ∈ Hf', pair a b ∈ Set.range (algebraMap O F)) ↔ a ∈ Hf
def StatBKc : Prop :=
  ∀ (O : Type) [CommRing O] (ϖ : O) (r : ℕ) (Hr HD HV Z H0 : Type) [AddCommGroup Hr] [Module O Hr]
    [AddCommGroup HD] [Module O HD] [AddCommGroup HV] [Module O HV] [AddCommGroup Z] [Module O Z]
    [AddCommGroup H0] [Module O H0] (io : Hr →ₗ[O] HD) (pr : HV →ₗ[O] HD) (j : Z →ₗ[O] HV)
    (q : Z →ₗ[O] Hr) (dl : H0 →ₗ[O] Z) (Hf : Submodule O HV),
    (∀ z, io (q z) = pr (j z)) → (∀ b : Hr, (ϖ ^ r) • b = 0) →
    (∀ β : HV, (ϖ ^ r) • pr β = 0 → ∃ z, j z = β) →
    (∀ b, io b = 0 → ∃ h, b = q (dl h)) → (∀ h, j (dl h) = 0) →
    ∀ b : Hr, (∃ β ∈ Hf, io b = pr β) → ∃ z : Z, j z ∈ Hf ∧ q z = b
end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic


