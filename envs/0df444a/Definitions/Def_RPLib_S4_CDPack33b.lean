-- Prove2me | Definitions.Def_RPLib_S4_CDPack33b
-- name    : RPLib_S4_CDPack33b
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T11:42:14.312193+00:00
-- url     : https://prove2.me/theorems/cbb9391f-6d57-4f2d-ac2c-87afe775329c
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 33b of 71
-- statement:
--   Part 33b of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_InstB`: S4-JacLaw, file O10e (part B): the `PreChunk` and group chunk of a `LawData`
--   * `Def_RP_JacLaw`: Weil's birational group law on `Sym^g X` (unit S4-JacLaw), umbrella
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack30e
import Definitions.Def_RPLib_S4_CDPack30y
import Definitions.Def_RPLib_S4_CDPack30w
import Definitions.Def_RPLib_S4_CDPack33
import Definitions.Def_RPLib_S4_CDPack29b

/-!
# Curve-duality library package, part 33b of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_InstB`: S4-JacLaw, file O10e (part B): the `PreChunk` and group chunk of a `LawData`
* `Def_RP_JacLaw`: Weil's birational group law on `Sym^g X` (unit S4-JacLaw), umbrella
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_InstB =====
section

/-!
# S4-JacLaw, file O10e (part B): the `PreChunk` and group chunk of a `LawData`

* `LawData.toPre L hw : PreChunk K S_g`; `hw` is one point of `D(ωm)` where `(a, m(a,b)) ∈ D(ωr)` and
  `(m(a,b), b) ∈ D(ωl)`.
* `LawData.chunk L hw : StrictChunk (sR K S_g[1/u0])`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk
open Algebra.TensorProduct (includeLeft includeRight)
open scoped TensorProduct

universe u

section Inst

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

namespace LawData

variable (L : LawData K F)

/-- The `PreChunk` of a `LawData`, given one witness point. -/
noncomputable def toPre
    (hw : ∃ x : Localization.Away L.ωm →ₐ[K] K, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0) :
    PreChunk K (SymRing K (Places.Rfin K F) (genusFK K F)) where
  ω := L.ωm
  μ := L.μm
  ωr := L.ωr
  ρ := L.ρr
  ωl := L.ωl
  la := L.lal
  r_m := L.rel_r_m
  m_r x' x := L.rel_m_r x x'
  l_m := L.rel_l_m
  m_l x' x := L.rel_m_l x x'
  assoc := L.rel_assoc
  wit := hw

/-- **The group chunk of the birational law** on `Spec S_g[1/u0]`. -/
noncomputable def chunk
    (hw : ∃ x : Localization.Away L.ωm →ₐ[K] K, x (phiS L.μm L.ωr) ≠ 0 ∧ x (psiS L.μm L.ωl) ≠ 0) :
    StrictChunk (k := K) (sR K (Localization.Away (L.toPre hw).u0)) :=
  (L.toPre hw).toStrict'

end LawData

end Inst

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw =====
section

/-!
# Weil's birational group law on `Sym^g X` (unit S4-JacLaw), umbrella

Milne III.7.1-7.2 (lemmas L15-L16 of `S4_COREB_ROUTE.md`). `S = S_g = SymRing K (Rfin K F) g` is the coordinate
ring of (an affine open of) `Sym^g X`.
* L15: `exists_lawData_wit` (files `Gen*`) produces law data `lawData K F`: the rule `(D, D') ↦ E` with
  `D + D' - g P0 ~ E` as a rational map `m` (`μm` on `D(ωm) ⊆ Sym^g × Sym^g`), and `r` (`ρr`) for the inverse,
  each well defined and unique on a dense open (files `Nu`, `Uniq`, `Step`, `Law`).
* L16: `lawPre K F : PreChunk K S` packages `m`, `r`, `l` with associativity and the inverse relations
  (`InstL*`, `InstR`, `InstA`, `Assoc`); `lawChunk K F` is the resulting strict group chunk on the dense open
  `D(u0) = Spec S[1/u0]` (`Shrink*`, `Sch`), stated in the form `StrictChunk (X ↘ Spec k)` used by S4-JacChunkB.
* The instances S4-JacChunkB needs on `X = Spec S[1/u0]`: reduced, irreducible, separated, locally of finite type,
  geometrically reduced; `dense_basicOpen_u0`: `D(u0)` is dense in `Spec S`.
-/

set_option autoImplicit false

open Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR
open CategoryTheory AlgebraicGeometry RamanujanPetersson.JacChunk

universe u

section Umb

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type u) [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- The law data of Weil's birational group law (L15), chosen by the genericity argument. -/
noncomputable def lawData : LawData K F := (exists_lawData_wit (K := K) (F := F)).choose

theorem lawData_hasWit : (lawData K F).HasWit := (exists_lawData_wit (K := K) (F := F)).choose_spec

/-- **Weil's birational group law** on `S_g` (L15-L16): `m`, `r`, `l`, associativity, inverse relations. -/
noncomputable def lawPre : PreChunk K (SymRing K (Places.Rfin K F) (genusFK K F)) :=
  (lawData K F).toPre (lawData_hasWit K F).out

theorem lawPre_u0_ne : (lawPre K F).u0 ≠ 0 := (lawPre K F).u0_ne

/-- The coordinate ring `S_g[1/u0]` of the dense open carrying the group chunk. -/
abbrev LawRing : Type u := Localization.Away (lawPre K F).u0

instance isDomain_lawRing : IsDomain (LawRing K F) := (lawPre K F).isDomain_u0

instance finiteType_lawRing : Algebra.FiniteType K (LawRing K F) :=
  Algebra.FiniteType.trans (S := SymRing K (Places.Rfin K F) (genusFK K F)) inferInstance inferInstance

/-- **The group chunk of Weil's law** on `X = Spec S_g[1/u0]` (L16), in the form used by S4-JacChunkB. -/
noncomputable def lawChunk : StrictChunk (k := K) (Spec (.of (LawRing K F)) ↘ Spec (.of K)) :=
  (lawPre K F).toStrict'

theorem lawChunk_eq : lawChunk K F = (lawData K F).chunk (lawData_hasWit K F).out := rfl

instance isReduced_lawX : IsReduced (Spec (.of (LawRing K F))) := inferInstance

instance irreducibleSpace_lawX : IrreducibleSpace (Spec (.of (LawRing K F))) := inferInstance

instance isSeparated_lawX : (Spec (.of (LawRing K F))).IsSeparated := inferInstance

instance isSeparated_lawX_hom : IsSeparated (Spec (.of (LawRing K F)) ↘ Spec (.of K)) := inferInstance

instance locallyOfFiniteType_lawX : LocallyOfFiniteType (Spec (.of (LawRing K F)) ↘ Spec (.of K)) :=
  inferInstance

instance geometricallyReduced_lawX : GeometricallyReduced (Spec (.of (LawRing K F)) ↘ Spec (.of K)) :=
  geometricallyReduced_sR (K := K) (R := LawRing K F)

/-- `D(u0)` is the image of `Spec S_g[1/u0] → Spec S_g`. -/
theorem range_lawRing :
    Set.range (PrimeSpectrum.comap (algebraMap (SymRing K (Places.Rfin K F) (genusFK K F)) (LawRing K F))) =
      (PrimeSpectrum.basicOpen (lawPre K F).u0 : Set (PrimeSpectrum (SymRing K (Places.Rfin K F) (genusFK K F)))) :=
  PrimeSpectrum.localization_away_comap_range (LawRing K F) (lawPre K F).u0

/-- `D(u0)` is a dense open of `Spec S_g`. -/
theorem dense_basicOpen_u0 :
    Dense (PrimeSpectrum.basicOpen (lawPre K F).u0 :
      Set (PrimeSpectrum (SymRing K (Places.Rfin K F) (genusFK K F)))) := by
  refine (PrimeSpectrum.basicOpen (lawPre K F).u0).isOpen.dense ?_
  rw [Set.nonempty_iff_ne_empty, ← TopologicalSpace.Opens.coe_bot, Ne, SetLike.coe_set_eq,
    PrimeSpectrum.basicOpen_eq_bot_iff]
  exact fun h => lawPre_u0_ne K F h.eq_zero

end Umb

end RamanujanPetersson.JacLaw

end


