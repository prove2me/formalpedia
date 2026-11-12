-- Prove2me | Definitions.Def_DSDensity1246_Main_dsModel
-- name    : DSDensity1246_Main_dsModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:10:33.939705+00:00
-- url     : https://prove2.me/theorems/bf7b73ce-1ffa-4f6e-adef-776f06ae45be
-- title:
--   Directional neighbors, list DS shattering, and extended DS dimension
-- statement:
--   Let $X$ and $Y$ be arbitrary sets and $H\subseteq Y^X$ a hypothesis class. For a sequence $S\in X^d$, its restriction $H|_S$ is the image of $H$ under $h\mapsto h\circ S$. Two words are $i$-neighbors when they differ at coordinate $i$ and agree at every other coordinate.
--
--   A finite family $F\subseteq Y^d$ is an $\ell$-DS witness when it is nonempty and every $f\in F$ has at least $\ell$ distinct $i$-neighbors in $F$ for every coordinate $i$. The class $H$ $\ell$-DS shatters $S$ when $H|_S$ contains such a family. For $\ell\ge1$, define
--
--   $$d^\ell_{\rm DS}(H)=\sup\{d\in\mathbb N:\exists S\in X^d,\ H\text{ $\ell$-DS shatters }S\}.$$
--
--   This definition measures local label richness without requiring a Cartesian box. The witness may be a proper subfamily of the restriction, and sample points may repeat.
--
--   **Formalization Note** The existing published projection is reused. Coordinates use $\mathrm{Fin}\,d$. The supremum takes values in $\mathbb N\cup\{\infty\}$, with empty supremum zero; hence the empty class has dimension zero. No finiteness or nonemptiness assumption is imposed on $X$, $Y$, or $H$.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 13, Definition 2; restriction convention in §3, pp. 12–13

import Definitions.Def_MulticlassDS_Compress_Dimensions

namespace DSDensity1246.Main

/-- Definition 2, p. 13: distinct words differing only in direction `i`. -/
def DirectionalNeighbor {Y : Type*} {n : ℕ}
    (i : Fin n) (f g : Fin n → Y) : Prop :=
  f i ≠ g i ∧ ∀ j, j ≠ i → f j = g j

/-- Definition 2: the finite nonempty witness, with at least `ℓ` distinct neighbors
in every direction. No Cartesian-box condition is imposed. -/
noncomputable def IsListDSWitness {Y : Type*} {n : ℕ}
    (ℓ : ℕ) (F : Finset (Fin n → Y)) : Prop := by
  classical
  exact F.Nonempty ∧ ∀ f ∈ F, ∀ i : Fin n,
    ℓ ≤ (F.filter (fun g => DirectionalNeighbor i f g)).card

/-- Definition 2: shattering of a sequence, allowing repeated points. -/
def ListDSShatters {X Y : Type*} {d : ℕ}
    (ℓ : ℕ) (H : Set (X → Y)) (S : Fin d → X) : Prop :=
  ∃ F : Finset (Fin d → Y),
    (↑F : Set (Fin d → Y)) ⊆ MulticlassDS.Compress.proj H S ∧
      IsListDSWitness ℓ F

/-- Definition 2: supremum of shattered lengths, with unbounded dimension `⊤`
and empty supremum `0`. -/
noncomputable def listDSDim {X Y : Type*} (ℓ : ℕ) (H : Set (X → Y)) : ℕ∞ :=
  ⨆ (d : ℕ) (S : Fin d → X) (_ : ListDSShatters ℓ H S), (d : ℕ∞)

end DSDensity1246.Main


