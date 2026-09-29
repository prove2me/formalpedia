-- Prove2me | Definitions.Def_ModularCurve_JHTwistedDatum
-- name    : ModularCurve_JHTwistedDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/dfacfdf0-6712-5700-9f37-67e7035ffd40
-- title:
--   Twisted fibre data and gluing datum for twist-type divisors
-- statement:
--   Fix a prime $p$ dividing $M$, a subgroup $H\le(\mathbb{Z}/M)^\times$ and a valuation subring $A\subset\overline{\mathbb{Q}}$ whose residue field $\kappa$ is algebraically closed of characteristic $p$; write $F_M$ for the geometric function field `xHFunctionFieldBar M H` and $\bar F$ for `Fbar p M H hpM κ`. Throughout, $SS$ is a finite set of pairs of places of $\bar F/\kappa$ (the node pairs), $e:SS\to\mathbb{N}$ the widths, $An$ an annulus over $A$ in $F_M$ for each $s\in SS$, $pos$ a rational position function on places of $F_M$, and $\alpha,\beta$ integral $\overline{\mathbb{Q}}$-algebra maps from the level-$M/p$ field together with a self-map $\delta$ of places of $\bar F$.
--
--   The structure `TwistedFibreDatum` records, for each $s\in SS$: two elements `unifFst s`, `unifSnd s` of $\bar F$, two divisors `corrFst s`, `corrSnd s` on $\bar F/\kappa$, and three units $u_0(s),\lambda(s),\mu(s)\in\kappa^\times$. The helper definitions attach to a divisor $D$ on $F_M/\overline{\mathbb{Q}}$ and $s\in SS$: the integer $\sum_{V\in\operatorname{supp}D\cap\operatorname{dom}An_s}D(V)$ (`twistAnnulusDeg`); the rational moment $\sum_{V}D(V)\,pos_s(V)$ (`twistPosMoment`); the flipped parameter $\pi_s\cdot z_s^{-1}$, with $\pi_s$ the annulus modulus and $z_s$ its parameter (`flipParam`); and the angular factor, which is the residue of $\bigl(\prod_V V(\pi_s/z_s)^{-D(V)}\bigr)\cdot p^{m}$ when the moment is an integer $m$ and that product lies in $A$ with nonzero residue, and $1$ otherwise. The cross values `twistCrossFst`, `twistCrossSnd` are the residue values of $s'$'s uniformisers at the first, resp. second, place of $s$ (junk value $1$ at a zero). Writing $o_1,o_2$ for the end orders `twistEndOrderFst`, `twistEndOrderSnd` of the twist vector $a$, the node unit is
--   $$(-1)^{\deg_s D}\,u_0(s)^{o_2(s)}\lambda(s)^{o_1(s)}\mu(s)^{-o_2(s)}\cdot\mathrm{ang}_s(D)\cdot\prod_{s'\ne s}\mathrm{cr}_1(s',s)^{-o_1(s')}\mathrm{cr}_2(s',s)^{o_2(s')},$$
--   viewed in $\kappa^\times$ additively. The two slots are the pushforwards along `reduceFst`, `reduceSnd` of the strict parts `fstDiv`, `sndDiv` of $D$, corrected by $\sum_s o_i(s)\cdot\mathrm{corr}_i(s)$; `twistSpData` is the resulting triple in `GluingData κ Fbar SS`, and `twistSp` its class in `GluedPic0`, set to $0$ when the triple fails admissibility. All of these are total definitions; the laws relating them are imposed by their consumers.
--
--   **Relation to Mathlib.** Mathlib provides the ambient objects only ($\mathsf{Finsupp}$-valued divisors, valuation subrings, `Additive`); annuli, gluing data, glued degree-zero Picard groups and twist vectors are the project's own notions.
--
--   **Where it is used.** These data describe the specialisation of a divisor class of twist type on $X_H(M)$ to the glued Picard group of the special fibre at $p$, i.e. the character-lattice and node-unit bookkeeping for $J_H$ at a prime dividing the level. They feed the level-lowering step (Mazur's principle) of the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JHTwistedDatum.lean

import Definitions.Def_ModularCurve_JHTwistType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

namespace ModularCurve
namespace JHPlaceSpecialization

structure TwistedFibreDatum {p M : ℕ} {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} {A : ValuationSubring (AlgebraicClosure ℚ)}
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) where

  unifFst : ↥SS → Fbar p M H hpM (ResidueField ↥A)

  unifSnd : ↥SS → Fbar p M H hpM (ResidueField ↥A)

  corrFst : ↥SS → Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))

  corrSnd : ↥SS → Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))

  u0 : ↥SS → (ResidueField ↥A)ˣ
  lam : ↥SS → (ResidueField ↥A)ˣ
  mu : ↥SS → (ResidueField ↥A)ˣ

section
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]
variable (Psp : JHPlaceSpecialization p M H hpM A)
  (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
  (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
  (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
  (e : ↥SS → ℕ) (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
  (pos : ↥SS → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℚ)
  (dat : TwistedFibreDatum (p := p) (M := M) (H := H) (hpM := hpM) (A := A) SS)

open Classical in

def twistAnnulusDeg (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℤ :=
  ∑ V ∈ D.support with V ∈ (An s).dom, D V

open Classical in

def twistPosMoment (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : ℚ :=
  ∑ V ∈ D.support with V ∈ (An s).dom, (D V : ℚ) * pos s V

def flipParam (s : ↥SS) : ↥(xHFunctionFieldBar M H) :=
  algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((((An s).modulus : ↥A) : AlgebraicClosure ℚ)) * ((An s).param)⁻¹

open Classical in

def twistAngFactor (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (s : ↥SS) : (ResidueField ↥A)ˣ :=
  if h : (twistPosMoment SS An pos D s).den = 1 ∧
      ∃ hmem : (∏ V ∈ D.support with V ∈ (An s).dom, (V.evalAt (flipParam SS An s)) ^ (-(D V))) *
          ((p : ℕ) : AlgebraicClosure ℚ) ^ (twistPosMoment SS An pos D s).num ∈ A,
        IsLocalRing.residue (R := ↥A) ⟨_, hmem⟩ ≠ 0
  then Units.mk0 (IsLocalRing.residue (R := ↥A) ⟨_, h.2.choose⟩) h.2.choose_spec else 1

open Classical in

def twistCrossFst (s' s : ↥SS) : (ResidueField ↥A)ˣ :=
  if h : (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1.evalAt (dat.unifFst s') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def twistCrossSnd (s' s : ↥SS) : (ResidueField ↥A)ˣ :=
  if h : (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2.evalAt (dat.unifSnd s') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def twistNodeUnit (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : ↥SS → Additive (ResidueField ↥A)ˣ := fun s =>
  Additive.ofMul <|
    (-1 : (ResidueField ↥A)ˣ) ^ (twistAnnulusDeg SS An D s) *
    dat.u0 s ^ (twistEndOrderSnd SS e An pos a D s) *
    dat.lam s ^ (twistEndOrderFst SS e An pos a D s) *
    (dat.mu s ^ (twistEndOrderSnd SS e An pos a D s))⁻¹ *
    twistAngFactor SS An pos D s *
    (∏ s' ∈ Finset.univ.erase s,
      (twistCrossFst SS dat s' s ^ (twistEndOrderFst SS e An pos a D s'))⁻¹ * twistCrossSnd SS dat s' s ^ (twistEndOrderSnd SS e An pos a D s'))

def twistFstSlot (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
  Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) - ∑ s : ↥SS, twistEndOrderFst SS e An pos a D s • dat.corrFst s

def twistSndSlot (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
  Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) - ∑ s : ↥SS, twistEndOrderSnd SS e An pos a D s • dat.corrSnd s

def twistSpData (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS :=
  (Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D) - ∑ s : ↥SS, twistEndOrderFst SS e An pos a D s • dat.corrFst s,
    Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D) - ∑ s : ↥SS, twistEndOrderSnd SS e An pos a D s • dat.corrSnd s,
    twistNodeUnit SS e An pos dat a D)

open Classical in

def twistSp (a : TwistVec ↥SS) (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS :=
  if h : twistSpData Psp α β hα hβ δ SS e An pos dat a D ∈ GluingData.admissible SS then GluedPic0.mk SS ⟨_, h⟩ else 0

end

end JHPlaceSpecialization
end ModularCurve

end


