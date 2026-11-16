-- Prove2me | Definitions.Def_CEPolytopeHard_Supplement_QueryAlg
-- name    : CEPolytopeHard_Supplement_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:12:19.981616+00:00
-- url     : https://prove2.me/theorems/aaa8f2c5-ed1c-4ac5-9116-de3cdf0010ea
-- title:
--   Deterministic adaptive utility-query algorithms, the utility oracle, and success
-- statement:
--   A **deterministic utility-query algorithm** on two-player games on $[0,1]^d$ is an adaptive procedure: given the list of responses received so far, it names the next query, a player $i\in\{1,2\}$ and a profile $(x,y)$; after its queries it outputs, as a function of all responses, a finite-support distribution on profiles. Computation between queries is free.
--
--   The **utility oracle** of a quadratic game $G$ answers the query $(i,(x,y))$ with $(x,y)\in[0,1]^d\times[0,1]^d$ by the value $u_i(x,y)$ and the own-strategy gradient $\nabla_{x_i}u_i(x,y)$ (value and subgradient oracles of Section 2.1). A run with budget $Q$ makes exactly $Q$ queries and returns the output on the resulting $Q$ responses.
--
--   An output distribution $\mu$ **solves** $G$ at $(C,c)$ when it is a $d^{-c}$-correlated equilibrium of $G$ (every deviation map $[0,1]^d\to[0,1]^d$) supported on at most $d^C$ profiles.
--
--   These notions are the query model of Theorem 3; a randomized algorithm is a family of deterministic algorithms indexed by a probability space of seeds.
--
--   **Formalization Note** The oracle is defined on the strategy space; a query outside it returns $(0,0)$. Responses lie in $\mathbb R\times\mathbb R^d$ (black-box real model).
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 3, p.5; Section 2.1, p.10 (black-box model, evaluation and subgradient oracles)

import Mathlib
import Definitions.Def_CEPolytopeHard_IsApproxCE
import Definitions.Def_CEPolytopeHard_Supplement_QuadGame

set_option autoImplicit false

namespace CEPolytopeHard.Supplement

/-- A **deterministic adaptive utility-query algorithm** on two-player games on `[0,1]^d`
(Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria
Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256
6aec500a…7820, Theorem 3, p.5, and the black-box model of Section 2.1, p.10: "Functions will
generally be given by evaluation oracles. If f : X → R is also guaranteed to be convex or concave,
we also assume access to an oracle for a subgradient ∇f : X → R^d").

Given the list of the responses received so far, `query` names the next query: a player `i` and a
profile `p`; `output` maps the full list of responses to a finitely supported distribution on
profiles (Section 2.1: "we will consider only finite-support distributions").

**Formalization Note** A response is a pair (value, own-strategy gradient) in `ℝ × ℝ^d`.
Computation between queries is free: `query` and `output` are arbitrary functions. -/
structure QueryAlg (d : ℕ) where
  /-- the next query (player, profile) as a function of the responses so far -/
  query : List (ℝ × (Fin d → ℝ)) → Fin 2 × (Fin 2 → Fin d → ℝ)
  /-- the output distribution as a function of all responses -/
  output : List (ℝ × (Fin d → ℝ)) → (Fin 2 → Fin d → ℝ) →₀ ℝ

namespace QueryAlg

variable {d : ℕ}

open Classical in
/-- The **utility oracle** of a quadratic game: the query `(i, p)` with `p ∈ [0,1]^d × [0,1]^d`
returns `(u_i(p), ∇_{p_i} u_i(p))`. The oracle is defined on the strategy space only; a query
outside it returns `(0, 0)`. -/
noncomputable def oracle (G : QuadGame d) (q : Fin 2 × (Fin 2 → Fin d → ℝ)) :
    ℝ × (Fin d → ℝ) :=
  if ∀ j, q.2 j ∈ box d then (G.utility q.1 q.2, G.ownGrad q.1 q.2) else (0, 0)

/-- the list of the first `k` responses of the run of `A` on `G` -/
noncomputable def transcript (A : QueryAlg d) (G : QuadGame d) : ℕ → List (ℝ × (Fin d → ℝ))
  | 0 => []
  | k + 1 => A.transcript G k ++ [oracle G (A.query (A.transcript G k))]

/-- the output of `A` on `G` after exactly `Q` queries -/
noncomputable def run (A : QueryAlg d) (G : QuadGame d) (Q : ℕ) : (Fin 2 → Fin d → ℝ) →₀ ℝ :=
  A.output (A.transcript G Q)

end QueryAlg

/-- An output `μ` **solves** the game `G` at `(C, c)` (Theorem 3, p.5): `μ` is a
`d^{−c}`-correlated equilibrium of `G` (`IsApproxCE`, every deviation map `[0,1]^d → [0,1]^d`)
supported on at most `d^C` profiles. -/
def SolvesCE (d : ℕ) (C c : ℝ) (G : QuadGame d) (μ : (Fin 2 → Fin d → ℝ) →₀ ℝ) : Prop :=
  IsApproxCE (E := fun _ : Fin 2 => Fin d → ℝ) (fun _ => box d) G.utility ((d : ℝ) ^ (-c)) μ ∧
    (μ.support.card : ℝ) ≤ (d : ℝ) ^ C

end CEPolytopeHard.Supplement


