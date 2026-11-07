-- Prove2me | Definitions.Def_BoolCSPDel_Sketch
-- name    : BoolCSPDel_Sketch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:46.43077+00:00
-- url     : https://prove2.me/theorems/64c38765-9cfe-4adf-bb25-eaf16fcc8425
-- title:
--   Public-coin linear sketches
-- statement:
--   A **linear sketch** has a public seed $\omega$ and a homomorphism $L_\omega:\mathbb Z^{U}\to G_\omega$ into a finite abelian group; the decoder receives $\omega$ and $L_\omega(f)$. Its **size** is $B=\sup_\omega\log_2|\mathrm{im}\,L_\omega|$; the seed is not charged.
--
--   **Formalization Note** The decoder's output type is a parameter: a Boolean for decisions, a set of constraints for exact sparsification.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), §3.2, p.18

import Mathlib

namespace BoolCSPDel

/-- **Public-coin linear sketches.** Bandekar, Sharma, Velusamy, STOC 2027 submission (manuscript
sha256 15f83519…), §3.2, p.18: "A linear sketch is specified by a public random seed `ω` and a
sketching map `L_ω : ℤ^{U_n} → Γ_ω` into a finite abelian group. The map is a homomorphism … The
decoder receives `ω` and `L_ω(f)` … We define the sketch size to be `B = sup_ω log₂ |im L_ω|`."

**Formalization Note.** The output type `O` is `Bool` for decisions and a set of constraints for exact
sparsification (§4.3, p.29). -/
structure Sketch (U Ω O : Type) where
  /-- The finite abelian group of each seed. -/
  G : Ω → Type
  [grp : ∀ ω, AddCommGroup (G ω)]
  [fin : ∀ ω, Finite (G ω)]
  /-- The sketching homomorphism. -/
  L : ∀ ω, (U → ℤ) →+ G ω
  /-- The decoder. -/
  dec : ∀ ω, G ω → O

attribute [instance] Sketch.grp Sketch.fin

/-- The decoder's output on the sketch of `f`. -/
def Sketch.out {U Ω O : Type} (σ : Sketch U Ω O) (ω : Ω) (f : U → ℤ) : O := σ.dec ω (σ.L ω f)

/-- `sup_ω log₂ |im L_ω| ≤ B`. -/
def Sketch.HasSize {U Ω O : Type} (σ : Sketch U Ω O) (B : ℝ) : Prop :=
  ∀ ω, Real.logb 2 (Nat.card (σ.L ω).range) ≤ B

end BoolCSPDel


