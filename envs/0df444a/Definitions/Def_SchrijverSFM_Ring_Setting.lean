-- Prove2me | Definitions.Def_SchrijverSFM_Ring_Setting
-- name    : SchrijverSFM_Ring_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:07.768338+00:00
-- url     : https://prove2.me/theorems/8c2c4269-a9f0-4e8b-80f1-6195cf15844c
-- title:
--   §6, pp. 353–354 — ring families, submodularity on 𝒞, closure X̄, M_v, L_v, the weights c of (23) and the function g of (26)
-- statement:
--   Let $V$ be a finite set. A collection $\mathcal C$ of subsets of $V$ is a **ring family** if it is closed under union and intersection: $X \cup Y \in \mathcal C$ and $X \cap Y \in \mathcal C$ for all $X, Y \in \mathcal C$. A function $f : 2^V \to \mathbb R$ is **submodular on $\mathcal C$** if the submodular inequality holds for sets of $\mathcal C$:
--   $$f(X \cup Y) + f(X \cap Y) \le f(X) + f(Y) \qquad (X, Y \in \mathcal C).$$
--   Nothing is required of $f$ on sets outside $\mathcal C$.
--
--   For a set $X \subseteq V$, its **closure** $\overline X$ is the intersection of all sets of $\mathcal C$ containing $X$; when $\mathcal C$ is a ring family with $V \in \mathcal C$, this is the smallest set of $\mathcal C$ containing $X$. For $v \in V$, $M_v := \overline{\{v\}}$ is the minimal set of $\mathcal C$ containing $v$, and $L_v$ is the union of all sets of $\mathcal C$ not containing $v$; when $\mathcal C$ is a ring family with $\emptyset \in \mathcal C$, $L_v$ is the largest set of $\mathcal C$ not containing $v$. The weights of display (23) are
--   $$c(v) := \max\{0,\ f(L_v) - f(L_v \cup \{v\})\} \qquad (v \in V),$$
--   extended modularly to sets by $c(X) := \sum_{v \in X} c(v)$ (the paper writes $c(X)$ for sets without restating this extension, which is its convention (4) for vectors). Finally, display (26) defines
--   $$g(X) := f(\overline X) + c(\overline X) \qquad (X \subseteq V).$$
--
--   These are the objects of Schrijver's reduction of submodular minimization over a ring family to submodular minimization over all subsets of $V$.
--
--   **Formalization Note** Subsets of $V$ are `Finset V` for a finite type `V` with decidable equality; $\mathcal C$ is a `Set (Finset V)` and $f$ is defined on all of `Finset V`, its values off $\mathcal C$ being arbitrary. The closure is `Finset.inf` of the sets of $\mathcal C$ containing $X$ (the empty infimum is $V$) and $L_v$ is `Finset.sup` of the sets of $\mathcal C$ avoiding $v$ (the empty supremum is $\emptyset$); under the standing hypotheses $\emptyset, V \in \mathcal C$ of the theorems these defaults are never reached.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), pp. 353–354, §6, displays (23) and (26)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
open Classical

namespace SchrijverSFM.Ring

/-- §6, p. 353: a **ring family** `C` on `V` is a collection of subsets of `V` closed under
union and intersection. -/
def IsRingFamily {V : Type} [Fintype V] [DecidableEq V] (C : Set (Finset V)) : Prop :=
  ∀ X ∈ C, ∀ Y ∈ C, X ∪ Y ∈ C ∧ X ∩ Y ∈ C

/-- §6, p. 353: `f` is submodular on `C`, i.e. the submodular inequality (2) holds for all sets
in `C` (and is not required elsewhere). -/
def SubmodularOn {V : Type} [Fintype V] [DecidableEq V] (C : Set (Finset V))
    (f : Finset V → ℝ) : Prop :=
  ∀ X ∈ C, ∀ Y ∈ C, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y

/-- §6, p. 354: `closure C X` is `X̄`, the smallest set of `C` containing `X`: the intersection of
all sets of `C` containing `X` (the empty intersection is `univ`; when `univ ∈ C` and `C` is a
ring family this is the smallest such set). -/
noncomputable def closure {V : Type} [Fintype V] [DecidableEq V] (C : Set (Finset V))
    (X : Finset V) : Finset V :=
  (Finset.univ.filter (fun Y => Y ∈ C ∧ X ⊆ Y)).inf id

/-- §6, p. 353: `M C v` is `M_v`, the minimal set of `C` containing `v`. -/
noncomputable def M {V : Type} [Fintype V] [DecidableEq V] (C : Set (Finset V)) (v : V) :
    Finset V :=
  closure C {v}

/-- §6, p. 353: `L C v` is `L_v`, the union of all sets of `C` not containing `v` (the empty union
is `∅`); for a ring family with `∅ ∈ C` it is the largest set of `C` not containing `v`. -/
noncomputable def L {V : Type} [Fintype V] [DecidableEq V] (C : Set (Finset V)) (v : V) :
    Finset V :=
  (Finset.univ.filter (fun Y => Y ∈ C ∧ v ∉ Y)).sup id

/-- §6, p. 353, display (23): `c(v) := max{0, f(L_v) − f(L_v ∪ {v})}`. -/
noncomputable def cw {V : Type} [Fintype V] [DecidableEq V] (C : Set (Finset V))
    (f : Finset V → ℝ) (v : V) : ℝ :=
  max 0 (f (L C v) - f (insert v (L C v)))

/-- The modular extension `c(X) := Σ_{v ∈ X} c(v)` of the weights (23), as in display (4). -/
noncomputable def csum {V : Type} [Fintype V] [DecidableEq V] (C : Set (Finset V))
    (f : Finset V → ℝ) (X : Finset V) : ℝ :=
  ∑ v ∈ X, cw C f v

/-- §6, p. 354, display (26): `g(X) := f(X̄) + c(X̄)` for `X ⊆ V`. -/
noncomputable def g {V : Type} [Fintype V] [DecidableEq V] (C : Set (Finset V))
    (f : Finset V → ℝ) (X : Finset V) : ℝ :=
  f (closure C X) + csum C f (closure C X)

end SchrijverSFM.Ring


