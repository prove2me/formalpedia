-- Prove2me | Definitions.Def_DSDensity1246_Main_Supplement_natarajan
-- name    : DSDensity1246_Main_Supplement_natarajan
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:22:54.31087+00:00
-- url     : https://prove2.me/theorems/83076935-c195-4029-bca6-65e70f87df85
-- title:
--   Scale-ℓ Natarajan shattering and extended dimension
-- statement:
--   Let H be a class of functions from X to Y, let ℓ be a natural number, and let S=(x₁,…,x_d) be an indexed sequence. The class ℓ-Natarajan shatters S if there are finite label sets Aᵢ of exactly ℓ+1 elements satisfying
--
--   $$\prod_{i=1}^{d} A_i\subseteq H|_S.$$
--
--   The scale-ℓ Natarajan dimension is the supremum of the lengths of all such sequences. Unlike a DS witness, a Natarajan witness requires the entire Cartesian box. This definition supplies the dimension used in both clauses of Theorem 8.
--
--   **Formalization Note** The dimension takes values in ℕ∞, so unbounded shattering gives infinity and the empty supremum is zero. Repeated sample points are permitted in the sequence representation. At length zero, the product contains the unique empty word, so an empty hypothesis class does not shatter that sequence.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 13, Definition 3

import Definitions.Def_MulticlassDS_Compress_Dimensions

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- Definition 3, p.13: full Cartesian boxes, with exactly ℓ+1 labels per coordinate. -/
def ListNatShatters {X Y : Type*} {d : ℕ} (ℓ : ℕ)
    (H : Set (X → Y)) (S : Fin d → X) : Prop :=
  ∃ A : Fin d → Finset Y, (∀ i, (A i).card = ℓ + 1) ∧
    ∀ w : Fin d → Y, (∀ i, w i ∈ A i) → w ∈ MulticlassDS.Compress.proj H S

/-- Extended dimension: unbounded shattering has dimension ⊤; the empty supremum is 0. -/
noncomputable def listNatDim {X Y : Type*} (ℓ : ℕ) (H : Set (X → Y)) : ℕ∞ :=
  ⨆ (d : ℕ) (S : Fin d → X) (_ : ListNatShatters ℓ H S), (d : ℕ∞)

end DSDensity1246.Main.Supplement


