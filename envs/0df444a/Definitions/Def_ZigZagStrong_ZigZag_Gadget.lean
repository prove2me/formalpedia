-- Prove2me | Definitions.Def_ZigZagStrong_ZigZag_Gadget
-- name    : ZigZagStrong_ZigZag_Gadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:04.471525+00:00
-- url     : https://prove2.me/theorems/6282ee71-98ff-4e52-a7a2-0a4c8a4abc61
-- title:
--   Finite gadget and determinant-defined sharp edge
-- statement:
--   A gadget $H$ is a finite undirected graph on $d$ ports with nonnegative integer adjacency counts and constant row sum $c$. Vertex transitivity means that adjacency-preserving port permutations act transitively. Goodness is the strict component-count condition on the graph of two-step walks, together with vertex transitivity.
--
--   Writing $A_H$ for the unnormalized adjacency matrix, the sharp-edge data are
--   $$h_H(x)=\det(xI-A_H^2),\quad Z_H(x)=x\sqrt{1-\frac{d h_H(x)}{x h'_H(x)}},\quad \Lambda_H=\inf_{x>c^2}Z_H(x).$$
--   The sharp-edge theorem includes attainment of this infimum, recovering the minimum in the paper. These definitions retain disconnected gadgets, loops and parallel incidences and provide the common finite input for every model.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), §3.1, Eq. (7), p. 11; standing hypotheses from CCM24 Definition 5.1 and Theorem 5.2.

import Mathlib

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open scoped BigOperators

/-- Finite undirected incidence-count gadget; loops and parallel incidences are retained.
Source: submission #371, §§1,3; CCM24 §4.1. -/
structure Gadget (d c : ℕ) where
  edges : Matrix (Fin d) (Fin d) ℕ
  symmetric : edges.IsSymm
  regular : ∀ i, ∑ j, edges i j = c

def Gadget.mat {d c : ℕ} (H : Gadget d c) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => H.edges i j

def VertexTransitive {d c : ℕ} (H : Gadget d c) : Prop :=
  ∀ i j, ∃ e : Equiv.Perm (Fin d), e i = j ∧ ∀ a b, H.edges (e a) (e b) = H.edges a b

def twoStepGraph {d c : ℕ} (H : Gadget d c) : SimpleGraph (Fin d) where
  Adj i j := i ≠ j ∧ 0 < (H.edges * H.edges) i j
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm, ?_⟩
    have heq : (H.edges * H.edges) j i = (H.edges * H.edges) i j := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      have hs (a b : Fin d) : H.edges a b = H.edges b a :=
        congrArg (fun A : Matrix (Fin d) (Fin d) ℕ => A b a) H.symmetric.eq
      rw [hs j k, hs k i, Nat.mul_comm]
    rw [heq]
    exact h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- CCM24 Definition 5.1, without any connectivity or non-bipartiteness assumption. -/
def Good {d c : ℕ} (H : Gadget d c) : Prop :=
  VertexTransitive H ∧ 2 * Nat.card (twoStepGraph H).ConnectedComponent < d

def sharpPolynomial {d c : ℕ} (H : Gadget d c) : Polynomial ℝ :=
  Matrix.charpoly ((fun i j => (H.edges i j : ℝ)) ^ 2)

def edgeFunction {d c : ℕ} (H : Gadget d c) (x : ℝ) : ℝ :=
  x * Real.sqrt (1 - (d : ℝ) * (sharpPolynomial H).eval x /
    (x * (sharpPolynomial H).derivative.eval x))

/-- Eq. (7). Attainment is part of the sharp-edge theorem, never a hypothesis. -/
def sharpEdge {d c : ℕ} (H : Gadget d c) : ℝ :=
  sInf (edgeFunction H '' Set.Ioi ((c : ℝ) ^ 2))
end ZigZagStrong.ZigZag


