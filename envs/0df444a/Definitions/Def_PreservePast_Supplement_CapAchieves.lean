-- Prove2me | Definitions.Def_PreservePast_Supplement_CapAchieves
-- name    : PreservePast_Supplement_CapAchieves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:27:22.224208+00:00
-- url     : https://prove2.me/theorems/2997d5ff-3035-4ff5-83d5-56a84d0e91be
-- title:
--   Cap classes in $(S^{D-1})^K$: $B$-bit protocols, the least width $B_\beta(\mathcal V,\theta)$, and the LP values $P_\beta$, $P^\ast_\beta$
-- statement:
--   A **cap class** is a nonempty finite or compact set $\mathcal V\subseteq(S^{D-1})^K$ of $K$-tuples of unit vectors of $\mathbb R^D$. A query $i\in[K]$ asks for a unit vector $T$ with $\langle v_i,T\rangle\ge\theta$.
--
--   A $B$-bit protocol **achieves error $\beta$** on $\mathcal V$ if, for every fixed history $v\in\mathcal V$ and query $i$, its unit response succeeds with probability at least $1-\beta$; the encoder and decoder are Borel measurable. $B_\beta(\mathcal V,\theta)$ is the least such width.
--
--   For a finite class $F$, $P_\beta(F)$ is the value of the fractional-subset LP with $X=F$, $Y=[K]$, legal actions the unit vectors and success $\langle v_i,T\rangle\ge\theta$, and
--   $$P^\ast_\beta(\mathcal V)=\sup_{F\subseteq\mathcal V\ \text{finite}}P_\beta(F).$$
--
--   **Formalization Note** The encoder is jointly measurable in the history and the coins. $B_\beta$ is an infimum of a set of natural numbers; Theorem 23 states the existence of an achieving protocol next to every use of it. The supremum defining $P^\ast_\beta$ runs over nonempty finite subclasses.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §P.2, p.73 (PDF p.75)

import Mathlib
import Definitions.Def_PreservePast_Supplement_ContractAchieves

open MeasureTheory
open scoped Classical

namespace PreservePast.Supplement

/-- The ambient space `(S^{D−1})^K` of cap classes: `K`-tuples of unit vectors of `ℝ^D`.
P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §P.2, p.73 (PDF p.75): "For finite or compact nonempty 𝒱 ⊆ (S^{D−1})^K". -/
def capSpace (K D : ℕ) : Set (Fin K → EuclideanSpace ℝ (Fin D)) := {v | ∀ i, ‖v i‖ = 1}

/-- **A B-bit protocol for a cap class** (the contract of `B_β(𝒱, θ)`). §P.2, p.73 (PDF p.75):
"a query i ∈ [K] asks for a unit T with ⟨v_i, T⟩ ≥ θ, 0 < θ < 1. Write B_β(𝒱, θ) for its
fixed-pair memory cost; on compact classes encoder and decoder must be Borel measurable."

**Formalization Note.** One coin space; the encoder is jointly measurable on `𝒱 × Ω` (Borel in the
history; for a finite class this is measurability in the coins for each history), the decoder is
measurable in the coins and always returns a unit vector; success has probability `≥ 1 − β` for
every fixed history in `𝒱` and query `i`. -/
def CapAchieves {K D B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (𝒱 : Set (Fin K → EuclideanSpace ℝ (Fin D))) (θ β : ℝ) (P : Measure Ω)
    (enc : (Fin K → EuclideanSpace ℝ (Fin D)) → Ω → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → Ω → Fin K → EuclideanSpace ℝ (Fin D)) : Prop :=
  IsProbabilityMeasure P ∧ Measurable (fun q : 𝒱 × Ω => enc q.1 q.2) ∧
    (∀ M i, Measurable (fun ω => dec M ω i)) ∧ (∀ M ω i, ‖dec M ω i‖ = 1) ∧
    ∀ v ∈ 𝒱, ∀ i, ENNReal.ofReal (1 - β) ≤ P {ω | θ ≤ inner ℝ (v i) (dec (enc v ω) ω i)}

/-- **The least width** `B_β(𝒱, θ)` of a cap class.

**Formalization Note.** `sInf` of a set of natural numbers (`0` if empty). Theorem 23 states the
existence of an achieving protocol next to every use of this number. -/
noncomputable def capWidth {K D : ℕ} (𝒱 : Set (Fin K → EuclideanSpace ℝ (Fin D))) (θ β : ℝ) : ℕ :=
  sInf {B : ℕ | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (enc : (Fin K → EuclideanSpace ℝ (Fin D)) → Ω → Fin (2 ^ B))
    (dec : Fin (2 ^ B) → Ω → Fin K → EuclideanSpace ℝ (Fin D)), CapAchieves 𝒱 θ β P enc dec}

/-- **The LP value** `P_β(F)` of a finite cap class `F`: the fractional-subset LP (270) with
`X = F`, `Y = [K]`, legal actions the unit vectors and success `⟨v_i, T⟩ ≥ θ` (§P.2: "Use
X = 𝒱, Y = [K] in the finite LP"). -/
noncomputable def capLP {K D : ℕ} (F : Finset (Fin K → EuclideanSpace ℝ (Fin D))) (θ β : ℝ) : ℝ :=
  lpValue (X := F) (Y := Fin K) (Act := EuclideanSpace ℝ (Fin D)) (fun _ => {T | ‖T‖ = 1})
    (fun v i T => θ ≤ inner ℝ (v.1 i) T) β

/-- `P*_β(𝒱) = sup_{F ⊆ 𝒱 finite} P_β(F)` (§P.2, p.73), over nonempty finite subclasses.

**Formalization Note.** A real `⨆`; for `0 < θ < 1` the values `P_β(F) ≤ P₀(F)` are bounded by
the net bound of the proof of Theorem 23, so this is a genuine supremum. -/
noncomputable def capLPStar {K D : ℕ} (𝒱 : Set (Fin K → EuclideanSpace ℝ (Fin D))) (θ β : ℝ) : ℝ :=
  ⨆ F : {F : Finset (Fin K → EuclideanSpace ℝ (Fin D)) // F.Nonempty ∧ (F : Set _) ⊆ 𝒱},
    capLP F.1 θ β

end PreservePast.Supplement


