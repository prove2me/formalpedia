-- Prove2me | Definitions.Def_RevRedSAT_reduceFam
-- name    : RevRedSAT_reduceFam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:34.242131+00:00
-- url     : https://prove2.me/theorems/890382b6-b4a5-4030-b6ac-e55ed2dbfc70
-- title:
--   Reduced families, layers, flowers and petals (Definitions B.1, B.2)
-- statement:
--   **Definition B.1.** The operation $\mathrm{reduce}(\mathcal F)$ removes duplicate sets and every set that strictly contains another member of $\mathcal F$. A family is **reduced** if this operation leaves it unchanged. Its **layer** of size $s$ is $\mathcal F_s=\{S\in\mathcal F:|S|=s\}$, and its **incidence length** is $\|\mathcal F\|=\sum_{S\in\mathcal F}|S|$.
--
--   **Definition B.2.** A **flower** in layer $\mathcal F_s$ is a nonempty subfamily $\mathcal Z$ whose full intersection $C=\bigcap_{S\in\mathcal Z}S$ is nonempty and has size less than $s$. $C$ is its **core**, $P(\mathcal Z)=\{S\setminus C:S\in\mathcal Z\}$ its family of **petals**, and $p=s-|C|$ its **petal size**. A flower need not be a sunflower: only the common intersection of the petals is empty.
--
--   For a threshold function $\theta$, "the layer contains no flower with at least $\theta(p)$ members" means every flower $\mathcal Z$ in $\mathcal F_s$ with petal size $p$ has $|\mathcal Z|<\theta(p)$.
--
--   **Formalization Note** Families are finite sets of subsets of $\{0,\dots,n-1\}$, so they never contain duplicates.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. B, Definitions B.1 and B.2, p.87

import Mathlib

set_option autoImplicit false

namespace RevRedSAT

/-- **The operation `reduce` (Definition B.1).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Definition B.1, p.87: "The
operation reduce(F) removes duplicate sets and every set that strictly contains another member of F.
A family is reduced if this operation leaves it unchanged. Its layer of size s is
F_s = {S ∈ F : |S| = s}, and its incidence length is ∥F∥ = Σ_{S∈F} |S|, the total number of element
occurrences in its sets."

**Formalization Note** Families are `Finset`s of subsets of `Fin n`, so they have no duplicates. -/
def reduceFam {n : ℕ} (F : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  F.filter fun S => ¬ ∃ T ∈ F, T ⊂ S

/-- A family is reduced if `reduce` leaves it unchanged (Definition B.1). -/
def IsReduced {n : ℕ} (F : Finset (Finset (Fin n))) : Prop := reduceFam F = F

/-- The layer `F_s = {S ∈ F : |S| = s}` (Definition B.1). -/
def layer {n : ℕ} (F : Finset (Finset (Fin n))) (s : ℕ) : Finset (Finset (Fin n)) :=
  F.filter fun S => S.card = s

/-- The incidence length `∥F∥ = Σ_{S ∈ F} |S|` (Definition B.1). -/
def incidenceLength {n : ℕ} (F : Finset (Finset (Fin n))) : ℕ := ∑ S ∈ F, S.card

/-- The full intersection `⋂_{S ∈ Z} S` of a subfamily (the core of a flower, Definition B.2). -/
def core {n : ℕ} (Z : Finset (Finset (Fin n))) : Finset (Fin n) := Z.inf id

/-- **A flower in the layer `F_s` (Definition B.2).** Definition B.2, p.87: "A flower in layer F_s is
a nonempty subfamily Z whose full intersection C = ⋂_{S∈Z} S is nonempty and has size less than s.
We call C its core, P(Z) = {S \ C : S ∈ Z} its family of petals, and p = s − |C| its petal size." -/
def IsFlower {n : ℕ} (F : Finset (Finset (Fin n))) (s : ℕ) (Z : Finset (Finset (Fin n))) : Prop :=
  Z ⊆ layer F s ∧ Z.Nonempty ∧ (core Z).Nonempty ∧ (core Z).card < s

/-- The petals `P(Z) = {S \ C : S ∈ Z}` of a flower with core `C` (Definition B.2). -/
def petals {n : ℕ} (Z : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  Z.image fun S => S \ core Z

/-- The layer `F_s` contains no flower `Z` with at least `θ(p)` members, `p = s − |core Z|` its petal
size: every flower `Z` in `F_s` has `|Z| < θ(p)`. With `θ = t` this is "sparse", with `θ = 2t`
"almost sparse" (Definition B.3). -/
def NoFlowerAtLeast {n : ℕ} (F : Finset (Finset (Fin n))) (s : ℕ) (θ : ℕ → ℝ) : Prop :=
  ∀ Z, IsFlower F s Z → (Z.card : ℝ) < θ (s - (core Z).card)

end RevRedSAT


