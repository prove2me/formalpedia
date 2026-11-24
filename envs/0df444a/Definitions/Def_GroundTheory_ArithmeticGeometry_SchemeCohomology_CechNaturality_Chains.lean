-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:05.789457+00:00
-- url     : https://prove2.me/theorems/c383bf32-6b29-4ec9-bd79-eb91c27777f2
-- title:
--   Chains
-- statement:
--   Definitions and structural lemmas for Chains, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechNaturality/Chains.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory
universe w
variable {ι : Type w}
abbrev Chain (ι : Type w) (n : ℕ) : Type w := (Fin (n + 1) → ι) →₀ ℤ
noncomputable def chainMap {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) : Chain ι n →+ Chain ι m :=
  Finsupp.mapDomain.addMonoidHom fun i => i ∘ θ
noncomputable def chainSimplicial (ι : Type w) : SimplicialObject AddCommGrpCat.{w} where
  obj n := AddCommGrpCat.of (Chain ι n.unop.len)
  map θ := AddCommGrpCat.ofHom (chainMap θ.unop.toOrderHom)
  map_id n := AddCommGrpCat.ext fun c => Finsupp.mapDomain_id
  map_comp θ θ' := AddCommGrpCat.ext fun c => by
    change Finsupp.mapDomain _ c = Finsupp.mapDomain _ (Finsupp.mapDomain _ c)
    rw [← Finsupp.mapDomain_comp]
    rfl
noncomputable def bd (n : ℕ) : Chain ι (n + 1) →+ Chain ι n :=
  (AlgebraicTopology.AlternatingFaceMapComplex.objD (chainSimplicial ι) n).hom
noncomputable def aug : Chain ι 0 →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ
noncomputable def lin {m n : ℕ} (f : (Fin (m + 1) → ι) → Chain ι n) : Chain ι m →+ Chain ι n :=
  Finsupp.liftAddHom fun j => zmultiplesHom _ (f j)
def rangeIn {n : ℕ} (S : Set ι) : Set (Fin (n + 1) → ι) := {j | Set.range j ⊆ S}
noncomputable def cone {n : ℕ} (s : ι) : Chain ι n →+ Chain ι (n + 1) :=
  Finsupp.mapDomain.addMonoidHom fun i => (Fin.cons s i : Fin (n + 2) → ι)
section Order
variable [LinearOrder ι]
def ordIn {n : ℕ} (S : Set ι) : Set (Fin (n + 1) → ι) := {j | StrictMono j ∧ Set.range j ⊆ S}
def ordFrom {n : ℕ} (s : ι) : Set (Fin (n + 1) → ι) := {j | StrictMono j ∧ s ≤ j 0}
noncomputable def ocone {n : ℕ} (s : ι) : Chain ι n →+ Chain ι (n + 1) :=
  Finsupp.liftAddHom fun i =>
    if s < i 0 then Finsupp.singleAddHom (Fin.cons s i : Fin (n + 2) → ι) else 0
noncomputable def minIdx {n : ℕ} (i : Fin (n + 1) → ι) : ι := Finset.univ.inf' Finset.univ_nonempty i
noncomputable def rho : (n : ℕ) → (Fin (n + 1) → ι) → Chain ι n
  | 0, i => Finsupp.single i 1
  | n + 1, i => ocone (minIdx i) (lin (rho n) (bd n (Finsupp.single i 1)))
noncomputable def hmt : (n : ℕ) → (Fin (n + 1) → ι) → Chain ι (n + 1)
  | 0, _ => 0
  | n + 1, i => cone (i 0)
      (Finsupp.single i 1 - rho (n + 1) i - lin (hmt n) (bd n (Finsupp.single i 1)))
end Order
end GroundTheory.Arith.SchemeCoh


