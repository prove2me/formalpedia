-- Prove2me | Definitions.Def_WeilConjectures_Etale_BaseChange
-- name    : WeilConjectures_Etale_BaseChange
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T12:15:05.578862+00:00
-- url     : https://prove2.me/theorems/be495192-c067-5860-8d1d-1c285177963a
-- title:
--   The geometric fibre $X_{\bar k}=X\times_k\bar k$ and the relative Frobenius $F\colon X_{\bar k}\to X_{\bar k}$
-- statement:
--   Let $k$ be a finite field of characteristic $p$ with algebraic closure $\bar k$, and $f\colon X\to\operatorname{Spec}k$ a $k$-scheme.
--
--   * $X_{\bar k}=X\times_{\operatorname{Spec}k}\operatorname{Spec}\bar k$, with its projection to $\operatorname{Spec}\bar k$.
--   * For $m\ge 0$, the iterated **relative Frobenius** $F^m=F_X^m\times_k\mathrm{id}_{\bar k}\colon X_{\bar k}\to X_{\bar k}$, where $F_X^m$ is the $q^m$-power Frobenius of $X$ (it commutes with $f$). It is a $\bar k$-morphism. The relative Frobenius is $F=F^1$.
--
--   For $X$ of finite type, the fixed points of $F^m$ on $X_{\bar k}(\bar k)$ are the $\mathbb F_{q^m}$-points of $X$; this is what makes $F$ the operator of the Lefschetz trace formula.
-- source:
--   P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), §1, (1.5); P. Deligne, SGA 4½, « Rapport sur la formule des traces ».

import Mathlib
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_FiniteFields_Dwork_Foundations
import Definitions.Def_FiniteFields_Schemes_GeneralFrobenius

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.Etale

variable {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of k))

variable (k) in
/-- `Spec k̄ ⟶ Spec k`. -/
def toBase : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- **D1.** `X_k̄ = X ×_k Spec k̄`. -/
abbrev geom : Scheme.{0} := pullback f (toBase k)

/-- La projection `X_k̄ ⟶ Spec k̄`. -/
abbrev geomToSpec : geom f ⟶ Spec (.of (AlgebraicClosure k)) := pullback.snd f (toBase k)

/-- Le Frobenius absolu `Fr_X^m` commute à la structure : `Fr_X^m ≫ f = f`. -/
theorem frob_comp (m : ℕ) : FiniteFields.Schemes.qPowerFrobenius p (Over.mk f) m ≫ f = f :=
  Over.w (FiniteFields.Schemes.qPowerFrobenius_over p (Over.mk f) m)

/-- **D2.** Les itérés du Frobenius relatif : `F^m = Fr_X^m ×_k id_{k̄}`. -/
def geomFrobPow (m : ℕ) : geom f ⟶ geom f :=
  pullback.map f (toBase k) f (toBase k) (FiniteFields.Schemes.qPowerFrobenius p (Over.mk f) m)
    (𝟙 _) (𝟙 _) (by rw [Category.comp_id, frob_comp]) (by simp)

/-- **D2.** Le Frobenius relatif `F : X_k̄ ⟶ X_k̄`. -/
abbrev geomFrob : geom f ⟶ geom f := geomFrobPow p f 1

/-- `F^m` est un `k̄`-morphisme. -/
@[reassoc (attr := simp)]
theorem geomFrobPow_toSpec (m : ℕ) : geomFrobPow p f m ≫ geomToSpec f = geomToSpec f := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)



end WeilConjectures.Etale


