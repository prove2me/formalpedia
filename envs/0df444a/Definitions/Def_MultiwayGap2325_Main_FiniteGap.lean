-- Prove2me | Definitions.Def_MultiwayGap2325_Main_FiniteGap
-- name    : MultiwayGap2325_Main_FiniteGap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:35.141051+00:00
-- url     : https://prove2.me/theorems/acb08c3f-bf26-4337-a83b-2d36f9529633
-- title:
--   Finite CKR optima, undirected normalization and the gap sequence
-- statement:
--   For an instance $I$ with nonnegative real weights and distinct terminals, let
--   $$
--   \operatorname{OPT}(I)=\inf\{\operatorname{cost}(c):c\text{ fixes the terminals}\},\qquad
--   \operatorname{LP}(I)=\inf\{\textstyle\sum_{uv}w_{uv}\tfrac12\|x_u-x_v\|_1:x\text{ is feasible in (2)}\}.
--   $$
--   The feasible embeddings use the entire real simplex. Define $\operatorname{gap}(I)$ to be $\operatorname{OPT}(I)/\operatorname{LP}(I)$ when the denominator is nonzero and 1 otherwise. For $k\ge2$, $G_k$ is the supremum over every finite vertex count and every such instance. Define $\beta=159389999561650025/129321858575204877$. The predicate $\operatorname{AsymptoticGapAtLeast}(b)$ asserts actual convergence to some $g\ge b$, together with a finite witness of gap at least $b-\eta$ for every sufficiently large $k$ and every $\eta>0$.
--
--   Reindexing transports every edge and terminal along a vertex equivalence. Normalization combines opposite orientations by adding their weights and removes loops. These operations make the finite-vertex and undirected conventions explicit.
--
--   **Formalization Note** Infima and suprema are real. Their well-posedness, attainment and zero-denominator properties are separate open supporting statements; none is assumed inside a definition. The entries $G_0,G_1$ are set to 1 solely to give a total sequence; all claimed gap identities concern $k\ge2$.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), §1, pp. 1–2, equations (1),(2), Theorem 1.1 and footnote 1; Appendix A, p. 34

import Definitions.Def_MultiwayCut_Instance

noncomputable section

namespace MultiwayGap2325.Main

/-- The objective values of all feasible integral labelings, §1, equation (1). -/
def integralValues {V : Type*} {k : ℕ} (I : MultiwayCut.Instance V k) : Set ℝ :=
  {r | ∃ c : V → Fin k, MultiwayCut.IsFeasibleLabeling I c ∧
    r = MultiwayCut.cutWeight I c}

/-- The objective values of all feasible embeddings into the full real simplex, equation (2). -/
def fractionalValues {V : Type*} {k : ℕ} (I : MultiwayCut.Instance V k) : Set ℝ :=
  {r | ∃ x : V → Fin k → ℝ, MultiwayCut.IsFeasibleEmbedding I x ∧
    r = MultiwayCut.relaxValue I x}

/-- Integral optimum computed from the graph, not an optimization certificate supplied as data. -/
def integralOpt {V : Type*} {k : ℕ} (I : MultiwayCut.Instance V k) : ℝ :=
  sInf (integralValues I)

/-- CKR optimum computed over all feasible real embeddings. -/
def fractionalOpt {V : Type*} {k : ℕ} (I : MultiwayCut.Instance V k) : ℝ :=
  sInf (fractionalValues I)

/-- The zero-LP convention is 1. Feasibility and the zero-LP implication are separate obligations. -/
def instanceGap {V : Type*} {k : ℕ} (I : MultiwayCut.Instance V k) : ℝ :=
  if fractionalOpt I = 0 then 1 else integralOpt I / fractionalOpt I

/-- Every finite vertex count is allowed and every nonnegative real weight is allowed. -/
def finiteGapValues (k : ℕ) : Set ℝ :=
  {r | ∃ n : ℕ, ∃ I : MultiwayCut.Instance (Fin n) k, r = instanceGap I}

/-- Positive-LP ratios, used to check that the zero-LP convention changes no supremum. -/
def positiveGapValues (k : ℕ) : Set ℝ :=
  {r | ∃ n : ℕ, ∃ I : MultiwayCut.Instance (Fin n) k,
    0 < fractionalOpt I ∧ r = integralOpt I / fractionalOpt I}

/-- G_k for k≥2. The first two sequence entries are set to 1 and play no role at infinity. -/
def gapSequence (k : ℕ) : ℝ :=
  if 2 ≤ k then sSup (finiteGapValues k) else 1

/-- The exact rational in Theorem 1.1; no decimal rounding. -/
def beta : ℝ := 159389999561650025 / 129321858575204877

/-- Both clauses of the asymptotic conclusion, with an actual convergent sequence. -/
def AsymptoticGapAtLeast (b : ℝ) : Prop :=
  ∃ g : ℝ, Filter.Tendsto gapSequence Filter.atTop (nhds g) ∧ b ≤ g ∧
    ∀ η : ℝ, 0 < η → ∃ K : ℕ, 2 ≤ K ∧ ∀ k : ℕ, K ≤ k →
      ∃ n : ℕ, ∃ I : MultiwayCut.Instance (Fin n) k, b - η ≤ instanceGap I

/-- Reindex a graph along a vertex equivalence, without changing any edge weights. -/
def reindex {V W : Type*} {k : ℕ} [DecidableEq W]
    (I : MultiwayCut.Instance V k) (e : V ≃ W) : MultiwayCut.Instance W k where
  E := I.E.image (fun a => (e a.1, e a.2))
  w := fun a => I.w (e.symm a.1, e.symm a.2)
  w_nonneg := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simpa using I.w_nonneg b hb
  t := fun i => e (I.t i)
  t_injective := e.injective.comp I.t_injective

/-- Store each undirected edge in its increasing orientation. Loops are removed. -/
def normalize {n k : ℕ} (I : MultiwayCut.Instance (Fin n) k) :
    MultiwayCut.Instance (Fin n) k where
  E := (I.E.image (fun e => (min e.1 e.2, max e.1 e.2))).filter (fun e => e.1 < e.2)
  w := fun e => ∑ a ∈ I.E,
    if (min a.1 a.2, max a.1 a.2) = e then I.w a else 0
  w_nonneg := by
    intro e he
    apply Finset.sum_nonneg
    intro a ha
    split_ifs
    · exact I.w_nonneg a ha
    · exact le_rfl
  t := I.t
  t_injective := I.t_injective

end MultiwayGap2325.Main


