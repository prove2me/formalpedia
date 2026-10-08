-- Prove2me | Definitions.Def_MulticlassDS_Compress_Compression
-- name    : MulticlassDS_Compress_Compression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:44:40.964298+00:00
-- url     : https://prove2.me/theorems/26e1c6a3-a913-4436-ab78-79c05a364964
-- title:
--   Definitions 30, 33, 35, 37, 38, pp. 19–23 — realizable samples, menus, (list / menu) sample compression schemes
-- statement:
--   Let $\mathcal H \subseteq \mathcal Y^{\mathcal X}$. A **sample** of size $n$ is a sequence $S = ((x_1,y_1),\dots,(x_n,y_n)) \in (\mathcal X \times \mathcal Y)^n$; it is **$\mathcal H$-realizable** if some $h \in \mathcal H$ has $h(x_i) = y_i$ for every $i$. A sequence $S' \in (\mathcal X\times\mathcal Y)^r$ is a **subsample** of $S$ ("its elements appear in $S$") if each entry of $S'$ is an entry of $S$; repetitions and any order are allowed.
--
--   1. **Menus** (Definitions 30, 33). A *menu of size $p$* is a map $\mu : \mathcal X \to \{Y \subseteq \mathcal Y : |Y| \le p\}$. A sample is *realizable by $\mu$* if $y_i \in \mu(x_i)$ for every $i$.
--   2. **Sample compression scheme** (Definition 35). A reconstruction function $\rho : (\mathcal X\times\mathcal Y)^r \to \mathcal Y^{\mathcal X}$ is an *$n \to r$ sample compression scheme* for $\mathcal H$ if for every $\mathcal H$-realizable $S \in (\mathcal X\times\mathcal Y)^n$ there is a subsample $S' \in (\mathcal X\times\mathcal Y)^r$ of $S$ with $\rho(S')(x) = y$ for every $(x,y)$ in $S$.
--   3. **List sample compression scheme with menu size $p$** (Definition 37). $\rho : (\mathcal X\times\mathcal Y)^r \to \{Y \subseteq \mathcal Y : |Y|\le p\}^{\mathcal X}$ such that every $\mathcal H$-realizable $S$ of size $n$ has a subsample $S'$ of size $r$ with $y \in \rho(S')(x)$ for every $(x,y)$ in $S$.
--   4. **Sample compression scheme for a menu** (Definition 38). $\rho : (\mathcal X\times\mathcal Y)^r \to \mathcal Y^{\mathcal X}$ such that every $S$ of size $n$ realizable by both $\mathcal H$ and $\mu$ has a subsample $S'$ of size $r$ with $\rho(S')(x) = y$ for every $(x,y)$ in $S$.
--
--   In each case the reconstruction function $\rho$ is fixed first and must work for every sample. The size $r$ of the compressed sample controls generalization, which is how compression yields PAC learning.
--
--   **Formalization Note** Samples are functions `Fin n → X × Y`. Menu sizes are measured with `Set.encard`, so an infinite set of labels never counts as small. Definition 35's requirement $r \le n$ is not part of the predicate `IsCompressionScheme` (Definitions 37 and 38 do not have it); it is stated in the goal theorem. In a list scheme the size bound $|\rho(S')(x)| \le p$ holds for every input $S'$ and every $x$, as the codomain on the page says.
-- source:
--   Brukhim, Carmon, Dinur, Moran, Yehudayoff, A Characterization of Multiclass Learnability, arXiv:2203.01550v1, p. 3 (realizable samples), p. 19 Definition 30, p. 20 Definition 33, p. 22 Definition 35, p. 23 Definitions 37, 38

import Mathlib

namespace MulticlassDS.Compress

/-- p. 3: a sample `S ∈ (X × Y)ⁿ` is `H`-realizable if some `h ∈ H` has `h(x) = y` for every
`(x, y)` in `S`. -/
def IsRealizable {X Y : Type*} {n : ℕ} (H : Set (X → Y)) (S : Fin n → X × Y) : Prop :=
  ∃ h ∈ H, ∀ i, h (S i).1 = (S i).2

/-- Definitions 35, 37, 38, p. 22–23: `S' ∈ (X × Y)ʳ` "has its elements appear in `S`"
(repetitions and any order allowed). -/
def IsSubsampleOf {X Y : Type*} {r n : ℕ} (S' : Fin r → X × Y) (S : Fin n → X × Y) : Prop :=
  ∀ j, ∃ i, S' j = S i

/-- Definition 30, p. 19: `μ : X → {Y ⊆ 𝒴 : |Y| ≤ p}` is a menu of size `p`. -/
def IsMenu {X Y : Type*} (μ : X → Set Y) (p : ℕ) : Prop :=
  ∀ x, (μ x).encard ≤ p

/-- Definition 33, p. 20: the sample `S` is realizable by the menu `μ` if `y ∈ μ(x)` for every
`(x, y)` in `S`. -/
def MenuRealizable {X Y : Type*} {n : ℕ} (μ : X → Set Y) (S : Fin n → X × Y) : Prop :=
  ∀ i, (S i).2 ∈ μ (S i).1

/-- Definition 35, p. 22: `ρ : (X × Y)ʳ → Y^X` is an `n → r` sample compression scheme for `H`:
every `H`-realizable `S ∈ (X × Y)ⁿ` has a subsample `S'` of length `r` whose reconstruction
`ρ(S')` labels every example of `S` correctly. (The constraint `r ≤ n` is stated separately.) -/
def IsCompressionScheme {X Y : Type*} (H : Set (X → Y)) (n r : ℕ)
    (ρ : (Fin r → X × Y) → X → Y) : Prop :=
  ∀ S : Fin n → X × Y, IsRealizable H S →
    ∃ S' : Fin r → X × Y, IsSubsampleOf S' S ∧ ∀ i, ρ S' (S i).1 = (S i).2

/-- Definition 37, p. 23: `ρ : (X × Y)ʳ → {Y ⊆ 𝒴 : |Y| ≤ p}^X` is an `n → r` list sample
compression scheme with menu size `p` for `H`. -/
def IsListCompressionScheme {X Y : Type*} (H : Set (X → Y)) (n r p : ℕ)
    (ρ : (Fin r → X × Y) → X → Set Y) : Prop :=
  (∀ (S' : Fin r → X × Y) (x : X), (ρ S' x).encard ≤ p) ∧
    ∀ S : Fin n → X × Y, IsRealizable H S →
      ∃ S' : Fin r → X × Y, IsSubsampleOf S' S ∧ ∀ i, (S i).2 ∈ ρ S' (S i).1

/-- Definition 38, p. 23: `ρ : (X × Y)ʳ → Y^X` is an `n → r` sample compression scheme for the
class `H` and the menu `μ`: it need only handle samples realizable by both `H` and `μ`. -/
def IsMenuCompressionScheme {X Y : Type*} (H : Set (X → Y)) (μ : X → Set Y) (n r : ℕ)
    (ρ : (Fin r → X × Y) → X → Y) : Prop :=
  ∀ S : Fin n → X × Y, IsRealizable H S → MenuRealizable μ S →
    ∃ S' : Fin r → X × Y, IsSubsampleOf S' S ∧ ∀ i, ρ S' (S i).1 = (S i).2

end MulticlassDS.Compress


