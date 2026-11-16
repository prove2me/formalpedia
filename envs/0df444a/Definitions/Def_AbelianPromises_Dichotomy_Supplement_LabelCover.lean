-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Supplement_LabelCover
-- name    : AbelianPromises_Dichotomy_Supplement_LabelCover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:54:16.328553+00:00
-- url     : https://prove2.me/theorems/7e1d7b18-f46b-4e4a-915e-72b7d4dda800
-- title:
--   Finite Label Cover, minion solutions, and the incidence construction
-- statement:
--   A finite Label Cover instance is a finite directed multigraph with a nonempty finite domain $X_v$ at each vertex and a total projection $\pi_e:X_v\to X_w$ for each directed edge $e:v\to w$. There is no bipartiteness, regularity, surjectivity, or common-alphabet assumption. Parallel edges, isolated vertices, and the empty vertex set are allowed. An $N$-solution chooses $f_v\in N^{(X_v)}$ with
--
--   $$
--   f_w=f_v^{\pi_e}\qquad(e:v\to w).
--   $$
--
--   The binary CSP of the graph has relation $\{(a,\pi_e(a)):a\in X_v\}$ on each edge, with source coordinate first. For a general current-domain CSP $I$, the incidence construction $\operatorname{LC}(I)$ has vertices for variables and constraints, with domains $D_x$ and $R_C$; each positional occurrence gives an edge from the constraint to its variable. The residual Label Cover instance after pruning keeps the original vertices, edges, and projection maps and restricts their domains. These interfaces are the ones appearing in Lemma C.12 and Definition C.13.
--
--   **Formalization Note** Raw intermediate data also allow empty domains so that rejection can be explicit. Only the initial Label Cover bundle requires nonempty domains and total projections. The existentially typed restriction of a projection must agree at every coordinate with the specified value map.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, STOC 2027 submission #967 (October 2026). Canonical submission artifact; no arXiv pin or acceptance claim. printed pp. 19–20 (PDF pp. 20–21), Section C.3, Label Cover and LC(I) definitions preceding Lemma C.12.

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Supplement_AbstractMinions
import Definitions.Def_AbelianPromises_Dichotomy_Supplement_Pruning

set_option autoImplicit false

namespace AbelianPromises.Dichotomy.Supplement

/-- Finite directed multigraph data, including parallel edges and isolated vertices.
Empty domains are representable for explicitly rejected intermediate instances. -/
structure LCData where
  n : ℕ
  m : ℕ
  domain : Fin n → Finset ℕ
  source : Fin m → Fin n
  target : Fin m → Fin n
  projection : Fin m → ℕ → ℕ

/-- The paper's initial finite Label Cover instances have nonempty finite domains
and total projections on those domains, with no surjectivity or bipartition assumption. -/
structure LabelCover extends LCData where
  domain_nonempty : ∀ v, (domain v).Nonempty
  projection_mem : ∀ (e : Fin m) (a : ℕ), a ∈ domain (source e) →
    projection e a ∈ domain (target e)

/-- An N-solution. A projection is the specified value map restricted to its domain,
not a new existential choice of a constraint. The existential supplies only its typing proof. -/
def LCData.HasSolution (L : LCData) (N : MinionPresentation) : Prop :=
  ∃ h : ∀ v, (L.domain v).Nonempty,
    ∃ f : (v : Fin L.n) → N.Obj ⟨L.domain v, h v⟩,
      ∀ e : Fin L.m,
        ∃ π : (⟨L.domain (L.source e), h (L.source e)⟩ : Arity) →
            (⟨L.domain (L.target e), h (L.target e)⟩ : Arity),
          (∀ a, (π a).val = L.projection e a.val) ∧
            N.IsMinor π (f (L.source e)) (f (L.target e))

/-- Reindex a finite multigraph into the base finite-instance conventions. -/
noncomputable def lcOf {V E : Type} [Fintype V] [Fintype E]
    (domain : V → Finset ℕ) (source target : E → V) (projection : E → ℕ → ℕ) : LCData where
  n := Fintype.card V
  m := Fintype.card E
  domain v := domain ((Fintype.equivFin V).symm v)
  source e := Fintype.equivFin V (source ((Fintype.equivFin E).symm e))
  target e := Fintype.equivFin V (target ((Fintype.equivFin E).symm e))
  projection e := projection ((Fintype.equivFin E).symm e)

/-- The binary projection CSP of a Label Cover instance, source coordinate first. -/
def labelCSP (L : LCData) : CurrentCSP where
  n := L.n
  m := L.m
  arity _ := 2
  scope e := ![L.source e, L.target e]
  domain := L.domain
  tuples e := (L.domain (L.source e)).image fun a => ![a, L.projection e a]

/-- Constraint labels enumerate the actual finite relation of that constraint. -/
noncomputable def tupleAt (I : CurrentCSP) (c : Fin I.m) (a : ℕ) :
    Fin (I.arity c) → ℕ := by
  classical
  exact if h : a < (I.rel c).card then
    ((Fintype.equivFin {t // t ∈ I.rel c}).symm
      (Fin.cast (by simp) ⟨a, h⟩)).val else fun _ => 0

/-- The associated LC(I): one vertex per variable and per constraint; one directed edge
from the constraint vertex to the variable vertex for every positional occurrence. -/
noncomputable def incidence (I : CurrentCSP) : LCData := by
  classical
  exact lcOf (V := Fin I.n ⊕ Fin I.m) (E := (c : Fin I.m) × Fin (I.arity c))
    (fun v => match v with
      | .inl x => I.domain x
      | .inr c => Finset.range (I.rel c).card)
    (fun e => Sum.inr e.1)
    (fun e => Sum.inl (I.scope e.1 e.2))
    (fun e a => tupleAt I e.1 a e.2)

/-- Retain the original vertices, edge occurrences, and projection value maps, restricting
only their domains to those of the pruned projection CSP. The finite pruning construction
preserves the array shape. The empty fallback makes this total even on unrelated raw data. -/
def residualLC (L : LCData) (J : CurrentCSP) : LCData :=
  { L with domain := fun v => if h : v.val < J.n then J.domain ⟨v.val, h⟩ else ∅ }

/-- The N-solution of kappa(L) on the original projection graph. None has no solution.
At the fixed point each surviving source value gives exactly its surviving edge tuple;
no incidence expansion is inserted into this output. -/
noncomputable def PrunedHasSolution (L : LCData) (N : MinionPresentation) : Prop :=
  match kappa (labelCSP L) with
  | none => False
  | some J => (residualLC L J).HasSolution N

end AbelianPromises.Dichotomy.Supplement


