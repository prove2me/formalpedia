-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:32.982912+00:00
-- url     : https://prove2.me/theorems/4dc1ba55-b4fa-43a8-b73e-964a3fff7614
-- title:
--   Isotropic Vanish
-- statement:
--   Definitions and structural lemmas for Isotropic Vanish, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/IsotropicVanish.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_HasSecondLogDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.C
section Defs4
variable {K : Type} [Field K]
def flin {σ : Type} (l linv : PowerSeries K) {n : Type} [Fintype n] (c : n → K)
    (u : n → MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (u j) l) linv
def EndInt (R : Subring K) (l linv : PowerSeries K) (a : K) : Prop := IntPS R (mulBy l linv a)
def Frame (R : Subring K) (l linv ph : PowerSeries K) : Prop :=
  IsLogPair l linv ∧ FGInt R l linv ∧ PowerSeries.constantCoeff ph = 0
variable [CharZero K]
def PhNormAt (R : Subring K) (l linv ph : PowerSeries K) (a b : K) : Prop :=
  Cong R (PowerSeries.subst (mulBy l linv a) ph) ((a * b) • ph)
def AdjAt (R : Subring K) (l linv ph : PowerSeries K) (a b : K) : Prop :=
  ∀ (σ : Type) (x y : MvPowerSeries σ K), IsPt R x → IsPt R y →
    Cong R (be0 l linv ph (fmul l linv a x) y) (be0 l linv ph x (fmul l linv b y))
def F1 (R : Subring K) (l linv ph : PowerSeries K) : Prop :=
  ∀ (σ : Type) (x x' y : MvPowerSeries σ K), IsPt R x → IsPt R x' → IsPt R y →
    Cong R (be0 l linv ph (fadd l linv x x') y) (be0 l linv ph x y + be0 l linv ph x' y)
def ZLinAt (R : Subring K) (l linv ph : PowerSeries K) (z : K) : Prop :=
  ∀ (σ : Type) (x y : MvPowerSeries σ K), IsPt R x → IsPt R y →
    Cong R (be0 l linv ph x (fmul l linv z y)) (z • be0 l linv ph x y)
end Defs4
def PtClosure : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (l linv : PowerSeries K),
    IsLogPair l linv → FGInt R l linv →
    (∀ (σ : Type) (x y : MvPowerSeries σ K), IsPt R x → IsPt R y → IsPt R (fadd l linv x y)) ∧
    (∀ a : K, EndInt R l linv a → ∀ (σ : Type) (x : MvPowerSeries σ K), IsPt R x →
      IsPt R (fmul l linv a x)) ∧
    EndInt R l linv 0 ∧ EndInt R l linv 1 ∧ EndInt R l linv (-1) ∧
    (∀ a b : K, EndInt R l linv a → EndInt R l linv b → EndInt R l linv (a + b)) ∧
    (∀ a b : K, EndInt R l linv a → EndInt R l linv b → EndInt R l linv (a * b))
def AdjFromNorm : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b : K),
    Frame R l linv ph → a ≠ 0 → EndInt R l linv a → EndInt R l linv a⁻¹ → EndInt R l linv b →
    PhNormAt R l linv ph a b → ZLinAt R l linv ph (a * b) → AdjAt R l linv ph a b
def AdjAdd : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K) (a b a' b' : K),
    Frame R l linv ph → F1 R l linv ph →
    EndInt R l linv a → EndInt R l linv b → EndInt R l linv a' → EndInt R l linv b' →
    AdjAt R l linv ph a b → AdjAt R l linv ph a' b' → AdjAt R l linv ph (a + a') (b + b')
def NormAdjAll : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    (∀ z : O, star z = z → ZLinAt R l linv ph (τ z)) →
    F1 R l linv ph → (2 : K)⁻¹ ∈ R → IsUnit (2 : O) →
    (∀ α : O, ∃ u v : Oˣ, α = u + v) →
    (∀ α : Oˣ, PhNormAt R l linv ph (τ α) (τ (star (α : O)))) →
    ∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α)) ∧ AdjAt R l linv ph (τ α) (τ (star α))
def UnitaryInv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    F1 R l linv ph →
    (∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (δ : Matrix n n O), δ.conjTranspose * δ = 1 →
    ∀ (σ : Type) (u : n → MvPowerSeries σ K), (∀ j, IsPt R (u j)) →
      Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (δ i j)) u) ph)
        (∑ j, PowerSeries.subst (u j) ph)
def IsotropicVanish : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    F1 R l linv ph →
    (∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] (f : ι → n → O),
    (∀ e e', ∑ i, star (f e i) * f e' i = 0) →
    ∀ (σ : Type) (t : ι → MvPowerSeries σ K), (∀ e, IsPt R (t e)) →
      LG R (∑ i, PowerSeries.subst (flin l linv (fun e => τ (f e i)) t) ph)
def HyperbolicSum : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    F1 R l linv ph →
    (∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] [DecidableEq ι] (f f' : ι → n → O),
    (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
    (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
    ∀ (σ : Type) (t t' : ι → MvPowerSeries σ K), (∀ e, IsPt R (t e)) → (∀ e, IsPt R (t' e)) →
      Cong R
        (∑ i, PowerSeries.subst
          (flin l linv (Sum.elim (fun e => τ (f e i)) (fun e => τ (f' e i))) (Sum.elim t t')) ph)
        (∑ e, be0 l linv ph (t e) (t' e))
end Formalism.L2.Th1.C


