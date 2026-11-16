-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Expander
-- name    : MTWalkSAT3CNF_TwoOcc_Supplement_Expander
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:57:25.725199+00:00
-- url     : https://prove2.me/theorems/741e5591-5327-41f8-ab30-1b5f3b98e29a
-- title:
--   The expander formula and active-block statistics
-- statement:
--   For a finite simple graph $G=(V,E)$, each vertex $v$ has progress bits $p_v,q_v$. For each progress bit and each of 52 indices, add fresh $a,b$ and all four clauses $(r_v\vee(\pm a)\vee(\pm b))$. For each of 613 indices add fresh $h$ and both $(p_v\vee q_v\vee(\pm h))$. For each directed edge $u\to v$ add $(p_v\vee\neg p_u\vee\neg q_u)$ and $(q_v\vee\neg p_u\vee\neg q_u)$. Each undirected edge contributes both orientations, and every auxiliary bit remains in the assignment space and uniform initialization.
--
--   The active set $S(x)$ has progress pair $(1,1)$; $Z_0(x)$ has pair $(0,0)$; $Z_1(x)$ has exactly one true progress bit. For disjoint $A,B$, $e_G(A,B)$ counts crossing edges once. The barrier constants are
--
--   $$\rho=451/486,\quad\gamma=\tfrac18\log_2(1/\rho),\quad K_N=\lfloor2^{\gamma N}\rfloor.$$
--
--   An explicit sufficient threshold is $N_0=\lceil\max(2\ln4,\log_2(4\cdot486/451)/\gamma)\rceil$. The formula and these statistics impose no runtime bounds.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, STOC 2027 submission #914 (October 2026), §6.1, pp. 36–37; §6.3, pp. 40–43; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Runtime
import Definitions.Def_MTWalkSAT3CNF_TwoOcc_Supplement_Graph

set_option autoImplicit false

namespace MTWalkSAT3CNF.TwoOcc.Supplement
open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Progress bits, four-clause auxiliary bits, and two-clause auxiliary bits. -/
abbrev ExpVar (N : ℕ) := (Fin N × Fin 2) ⊕
  ((Fin N × Fin 2 × Fin 52 × Fin 2) ⊕ (Fin N × Fin 613))

def progress {N : ℕ} (v : Fin N) (r : Fin 2) : ExpVar N := .inl (v,r)
def auxFour {N : ℕ} (v : Fin N) (r : Fin 2) (c : Fin 52) (ab : Fin 2) : ExpVar N :=
  .inr (.inl (v,r,c,ab))
def auxTwo {N : ℕ} (v : Fin N) (c : Fin 613) : ExpVar N := .inr (.inr (v,c))

abbrev DirectedEdge {N : ℕ} (G : SimpleGraph (Fin N)) :=
  {uv : Fin N × Fin N // G.Adj uv.1 uv.2}

abbrev ExpIndex {N : ℕ} (G : SimpleGraph (Fin N)) :=
  (Fin N × Fin 2 × Fin 52 × Fin 2 × Fin 2) ⊕
  ((Fin N × Fin 613 × Fin 2) ⊕ (DirectedEdge G × Fin 2))

noncomputable instance {N : ℕ} (G : SimpleGraph (Fin N)) : Fintype (ExpIndex G) := by
  classical
  dsimp [ExpIndex, DirectedEdge]
  infer_instance

/-- §6.1 direct construction. Every undirected edge supplies both directed edges. -/
def expClause {N : ℕ} (G : SimpleGraph (Fin N)) : ExpIndex G → Clause (ExpVar N)
  | .inl (v,r,c,s,t) =>
      triple (progress v r) (auxFour v r c 0) (auxFour v r c 1)
        true (decide (s.val = 0)) (decide (t.val = 0))
        (by simp [progress,auxFour]) (by simp [progress,auxFour]) (by simp [auxFour])
  | .inr (.inl (v,c,s)) =>
      triple (progress v 0) (progress v 1) (auxTwo v c)
        true true (decide (s.val = 0))
        (by simp [progress]) (by simp [progress,auxTwo]) (by simp [progress,auxTwo])
  | .inr (.inr (e,r)) =>
      triple (progress e.val.2 r) (progress e.val.1 0) (progress e.val.1 1)
        true false false
        (by simp [progress, (G.ne_of_adj e.property).symm])
        (by simp [progress, (G.ne_of_adj e.property).symm]) (by simp [progress])

noncomputable def expFormula {N : ℕ} (G : SimpleGraph (Fin N)) := indexed (expClause G)

def active {N : ℕ} (x : ExpVar N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun v => x (progress v 0) = true ∧ x (progress v 1) = true)
def zeroBlocks {N : ℕ} (x : ExpVar N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun v => x (progress v 0) = false ∧ x (progress v 1) = false)
def oneBlocks {N : ℕ} (x : ExpVar N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun v => x (progress v 0) ≠ x (progress v 1))

/-- For disjoint A,B, counts each undirected crossing edge once (oriented A to B). -/
noncomputable def cutCount {N : ℕ} (G : SimpleGraph (Fin N))
    (A B : Finset (Fin N)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun uv : Fin N × Fin N =>
    uv.1 ∈ A ∧ uv.2 ∈ B ∧ G.Adj uv.1 uv.2)).card

noncomputable def rho : ℝ := 451/486
noncomputable def gamma : ℝ := (1/8) * Real.logb 2 (1/rho)
noncomputable def barrierTime (N : ℕ) : ℕ := ⌊(2:ℝ) ^ (gamma*N)⌋₊

/-- An explicit sufficient threshold from the two error estimates on pp. 42--43. -/
noncomputable def separationThreshold : ℕ :=
  ⌈max (2*Real.log 4) (Real.logb 2 (4*486/451) / gamma)⌉₊

end MTWalkSAT3CNF.TwoOcc.Supplement


