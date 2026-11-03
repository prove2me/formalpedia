-- Prove2me | Definitions.Def_RandomOrderCRS_Regularize
-- name    : RandomOrderCRS_Regularize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:04.717534+00:00
-- url     : https://prove2.me/theorems/fa8aac42-8498-4916-a5bb-a946b8c404c4
-- title:
--   The 1-regular reduction: the graph $G'$ and the vector $x'$
-- statement:
--   Let $G=(V,E)$ with fractional matching $x$, and write $x_v:=\sum_{e\in\partial(v)}x_e$. For each vertex $v=v_0$, add six new vertices $v_1,\dots,v_6$ and the cycle $v_0,v_1,\dots,v_6,v_0$ of length 7. On the gadget edges set
--
--   $$x'_{v_i,v_{i+1}}:=\begin{cases}(1-x_{v})/2&i\text{ even},\\(1+x_{v})/2&i\text{ odd},\end{cases}\qquad i\in\{0,1,\dots,6\},$$
--
--   with $v_7=v_0$, and set $x'_e:=x_e$ on the original edges. This is the construction of the proof of Lemma EC.1. It pads every vertex to fractional degree exactly 1.
--
--   **Formalization Note** The new vertex set is `V × Fin 7`, the gadget vertex $v_i$ is `(v, i)`, and `v` is identified with `(v, 0)`; the cycle uses the cyclic addition of `Fin 7`. The vector $x'$ vanishes off the edges of $G'$. `NoCyclesOfLengthThreeOrFive` says that a graph has no cycle of length 3 or 5.
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Appendix C.1, proof of Lemma EC.1, ec14

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The graph `G′` of the 1-regular reduction, arXiv:2209.07520v2, proof of Lemma EC.1, ec14: "For
v0 ∈ V, we add 6 additional vertices, say v1, ..., v6, and create a cycle of length 7 of the form
v0, v1, ..., v6, v0."

**Formalization Note.** `V′` is `V × Fin 7`. The vertex `v_i` of the gadget at `v` is `(v, i)`, the
original vertex `v` is `(v, 0)`, and the cycle uses addition in `Fin 7`, which is cyclic. -/
def regularize (G : SimpleGraph V) : SimpleGraph (V × Fin 7) where
  Adj a b := (a.2 = 0 ∧ b.2 = 0 ∧ G.Adj a.1 b.1) ∨ (a.1 = b.1 ∧ (b.2 = a.2 + 1 ∨ a.2 = b.2 + 1))
  symm := ⟨by
    rintro a b (⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂⟩)
    · exact Or.inl ⟨h₂, h₁, h₃.symm⟩
    · exact Or.inr ⟨h₁.symm, h₂.symm⟩⟩
  loopless := ⟨by
    rintro a (⟨-, -, h⟩ | ⟨-, h⟩)
    · exact G.loopless.irrefl _ h
    · have key : ∀ i : Fin 7, i ≠ i + 1 := by decide
      exact h.elim (key _) (key _)⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (regularize G).Adj := fun a b => by
  unfold regularize
  simp only
  infer_instance

/-- The value on the gadget edge `(v_i, v_{i+1})`, arXiv:2209.07520v2, ec14: "we define
x′_{v_i,v_{i+1}} = (1 − x_{v0})/2 if i ∈ {0, 1, ..., 6} is even, and x′_{v_i,v_{i+1}} =
(1 + x_{v0})/2 if i is odd", where `x_{v0} := ∑_{e∈∂_G(v0)} x_e`. -/
noncomputable def gadgetValue (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ) (v : V)
    (i : Fin 7) : ℝ :=
  if (i : ℕ) % 2 = 0 then (1 - fracDegree G x v) / 2 else (1 + fracDegree G x v) / 2

/-- The value of `x′` on a pair of vertices of `V′`. -/
noncomputable def regularizeValue (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (a b : V × Fin 7) : ℝ :=
  if a.1 = b.1 then
    if b.2 = a.2 + 1 then gadgetValue G x a.1 a.2
    else if a.2 = b.2 + 1 then gadgetValue G x a.1 b.2
    else 0
  else if a.2 = 0 ∧ b.2 = 0 then x s(a.1, b.1)
  else 0

theorem regularizeValue_comm (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (a b : V × Fin 7) : regularizeValue G x a b = regularizeValue G x b a := by
  have key : ∀ i j : Fin 7, j = i + 1 → i = j + 1 → False := by decide
  unfold regularizeValue
  by_cases h : a.1 = b.1
  · have h' : b.1 = a.1 := h.symm
    simp only [h, if_true]
    split_ifs with h₁ h₂ h₃ <;> first | rfl | exact (key _ _ h₁ h₂).elim
  · have h' : ¬ b.1 = a.1 := fun hh => h hh.symm
    simp only [h, h', if_false, and_comm, Sym2.eq_swap (a := a.1) (b := b.1)]

/-- The vector `x′` of the 1-regular reduction, arXiv:2209.07520v2, ec14: the gadget values above,
and "we set x′_e := x_e for each e ∈ E". It vanishes off the edges of `G′`.

**Formalization Note.** `x′` is a function on `Sym2 (V × Fin 7)`, as for every vector here. -/
noncomputable def regularizeX (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ) :
    Sym2 (V × Fin 7) → ℝ :=
  Sym2.lift ⟨regularizeValue G x, regularizeValue_comm G x⟩

/-- `G` has no cycles of length 3 or 5 (arXiv:2209.07520v2, Lemma EC.1, clause 3, ec14). -/
def NoCyclesOfLengthThreeOrFive {W : Type} (G : SimpleGraph W) : Prop :=
  ∀ (v : W) (c : G.Walk v v), c.IsCycle → c.length ≠ 3 ∧ c.length ≠ 5

end RandomOrderCRS


