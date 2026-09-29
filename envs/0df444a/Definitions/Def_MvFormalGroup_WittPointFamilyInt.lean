-- Prove2me | Definitions.Def_MvFormalGroup_WittPointFamilyInt
-- name    : MvFormalGroup_WittPointFamilyInt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/c4fec619-d53b-509c-814e-097931edf5e4
-- title:
--   Witt-vector Frobenius on series points over any base
-- statement:
--   Throughout, $p$ is a prime, $R$ a commutative ring and $\tau$ a variable type, and `WittLaw.seriesPoint p R τ` is the additive subgroup of $p$-typical Witt vectors over `MvPowerSeries τ R` consisting of those $x$ all of whose components have vanishing constant coefficient and whose family of components $n \mapsto x_n$ is substitutable (`HasSubst`). The first group of declarations identifies the components of Mathlib's Witt-vector Frobenius in substitution terms: for any Witt vector $x$ over `MvPowerSeries τ R`, the $n$-th component of `WittVector.frobenius x` is obtained by substituting the family $m \mapsto x_m$ into the series `frobPolyFam p R n` (the image over $R$ of the integral Frobenius polynomial). Consequently the subgroup `seriesPoint p R τ` is stable under Frobenius, which yields the additive map `frobIntPt : seriesPoint p R τ →+ seriesPoint p R τ` whose underlying Witt vector is `WittVector.frobenius`, defined over an arbitrary base ring, together with its coefficient formula. Its basic identities are recorded: when $R$ has characteristic $p$ it coincides with the project's operator `frobPt`; `frobIntPt (verPt x) = p • x`; and `frobIntPt (teichPt c x) = teichPt (c ^ p) (frobIntPt x)` for $c \in R$, so Teichmüller scaling is transported with the scalar raised to the $p$-th power.
--
--   The second part records the adjunction with the Verschiebung of the Cartier module: for a commutative multivariate formal group law $\Phi$ of dimension $d$ over $R$, an element $f$ of `CartierModule p Φ` and a point $w$ of `seriesPoint p R τ`, one has $\mathrm{evalPt}\,f\,(\mathrm{frobIntPt}\,w) = \mathrm{evalPt}\,(\mathrm{verschiebungInt}\,f)\,w$, and the iterated form of the same identity for the $m$-fold iterates of the two operators.
--
--   **Relation to Mathlib.** Mathlib provides `WittVector.frobenius` over an arbitrary commutative ring, together with `WittVector.coeff_frobenius`, `WittVector.frobenius_verschiebung` and the Teichmüller compatibility; what is added here is the substitution description of its components and its restriction to the project's subgroup `seriesPoint` of Witt vectors with substitutable, constant-term-free power series components.
--
--   **Where it is used.** These operators supply the point-level counterpart of the Verschiebung on Cartier modules over base rings that need not have characteristic $p$, which is what Cartier's presentation of a formal group law by its module of $p$-typical curves requires in that generality. They feed the formal-group and Cartier-theory layer used further on in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_WittPointFamilyInt.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_WittPointFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v

open MvPowerSeries

namespace MvFormalGroup

namespace WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {τ : Type v}

theorem coeff_frobenius_eq_subst_frobPolyFam (x : WittVector p (MvPowerSeries τ R)) (n : ℕ) :
    (WittVector.frobenius x).coeff n = subst (fun m => x.coeff m) (frobPolyFam p R n) := by
  rw [WittVector.coeff_frobenius]
  change MvPolynomial.eval₂ (Int.castRingHom (MvPowerSeries τ R)) x.coeff (WittVector.frobeniusPoly p n) = _
  rw [frobPolyFam_apply, frobPoly_eq_map, subst_coe, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem frobenius_mem_int {x : WittVector p (MvPowerSeries τ R)} (hx : x ∈ seriesPoint p R τ) :
    WittVector.frobenius x ∈ seriesPoint p R τ := by
  have hfam : (fun n => (WittVector.frobenius x).coeff n) =
      fun n => subst (fun m => x.coeff m) (frobPolyFam p R n) :=
    funext (coeff_frobenius_eq_subst_frobPolyFam x)
  refine ⟨fun n => ?_, ?_⟩
  · rw [coeff_frobenius_eq_subst_frobPolyFam x]
    exact constantCoeff_subst_eq_zero hx.2 hx.1 (constantCoeff_frobPolyFam (p := p) (R := R) n)
  · rw [hfam]
    simpa only [coe_substAlgHom] using (hasSubst_frobPolyFam (p := p) (R := R)).comp hx.2

def frobIntPt : seriesPoint p R τ →+ seriesPoint p R τ where
  toFun x := ⟨WittVector.frobenius x, frobenius_mem_int x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp] theorem coe_frobIntPt (x : seriesPoint p R τ) :
    ((frobIntPt x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)) = WittVector.frobenius x :=
  rfl

theorem coeff_frobIntPt (x : seriesPoint p R τ) (n : ℕ) :
    ((frobIntPt x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n =
      subst (fun m => (x : WittVector p (MvPowerSeries τ R)).coeff m) (frobPolyFam p R n) :=
  coeff_frobenius_eq_subst_frobPolyFam (x : WittVector p (MvPowerSeries τ R)) n

theorem frobIntPt_eq_frobPt [CharP R p] (x : seriesPoint p R τ) : frobIntPt x = frobPt x :=
  Subtype.ext rfl

theorem frobIntPt_verPt (x : seriesPoint p R τ) : frobIntPt (verPt x) = p • x := by
  apply Subtype.ext
  rw [coe_frobIntPt, coe_verPt, WittVector.frobenius_verschiebung, AddSubgroup.coe_nsmul,
    nsmul_eq_mul, mul_comm]

theorem frobIntPt_teichPt (c : R) (x : seriesPoint p R τ) :
    frobIntPt (teichPt c x) = teichPt (c ^ p) (frobIntPt x) := by
  apply Subtype.ext
  rw [coe_frobIntPt, coe_teichPt, coe_teichPt, coe_frobIntPt, map_mul, WittVector.frobenius_teichmuller_eq,
    ← map_pow]

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}
  {τ : Type v}

theorem evalPt_frobIntPt [Φ.IsComm] (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) :
    evalPt f (WittLaw.frobIntPt w) = evalPt (verschiebungInt f) w :=
  evalPt_eq_evalPt_precomp WittLaw.isEndo_frobPolyFam f w _ fun n => WittLaw.coeff_frobIntPt w n

theorem evalPt_frobIntPt_iterate [Φ.IsComm] (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ)
    (m : ℕ) :
    evalPt f ((⇑(WittLaw.frobIntPt (p := p) (R := R) (τ := τ)))^[m] w) =
      evalPt ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] f) w := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply, evalPt_frobIntPt, ih]

end CartierModule

end MvFormalGroup

end


