-- Prove2me | Definitions.Def_TranspositionIID_Main_ListModel
-- name    : TranspositionIID_Main_ListModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:03.654717+00:00
-- url     : https://prove2.me/theorems/d1d9c463-c9bb-4079-8954-86b4eb019d4d
-- title:
--   IID transposition lists, query cost and actual optimum
-- statement:
--   A list $\sigma$ sends each of $n$ labels to its position. The requested label moves forward exactly one position by swapping with its predecessor; a request for the first label leaves the list unchanged. Independent requests with probabilities $p_i$ give
--   $$P_p(\sigma,\eta)=\sum_i p_i\mathbf1\{T_i\sigma=\eta\},\quad \operatorname{Cost}_p(\sigma)=\sum_i p_i\operatorname{position}_\sigma(i).$$
--   Define $\operatorname{OPT}_p=\min_\sigma\operatorname{Cost}_p(\sigma)$ and $F_p=\operatorname{Cost}_p-\operatorname{OPT}_p$. Decreasing means $p_i\ge p_j$ when $i<j$.
--   These definitions retain zero request probabilities and arbitrary initial lists. Positions use `Fin n` internally and charge the value plus one. The optimum is an infimum of a finite nonempty range, hence the attained minimum.
-- source:
--   Clayton Mizgerd, Transposition achieves OPT+O(1) in polynomial time for IID list update, STOC 2027 submission #668 (October 2026), supplied canonical submission artifact; citation basis published (not acceptance). §1, printed pp.1–2 = PDF pp.1–2, equation (1.1)

import Definitions.Def_TranspositionIID_Main_FiniteChain

noncomputable section

namespace TranspositionIID.Main

/-- Lists map zero-based labels to zero-based positions; charged positions add one. -/
abbrev ListState (n : ℕ) := Equiv.Perm (Fin n)

/-- The requested label moves one position forward, or stays if already first (§1, p.1). -/
def transposeRequest {n : ℕ} (σ : ListState n) (i : Fin n) : ListState n :=
  if h : 0 < (σ i).val then
    σ.trans (Equiv.swap (σ i) (⟨(σ i).val - 1, by omega⟩ : Fin n))
  else σ

/-- The exact IID request kernel, including zero probabilities. -/
def transpositionKernel {n : ℕ} (p : Fin n → ℝ) : Matrix (ListState n) (ListState n) ℝ :=
  fun σ η => ∑ i, if transposeRequest σ i = η then p i else 0

/-- Expected next query cost in a fixed list. -/
def cost {n : ℕ} (p : Fin n → ℝ) (σ : ListState n) : ℝ :=
  ∑ i, p i * ((σ i).val + 1 : ℕ)

/-- Actual finite attained optimum; the permutation type always contains the identity. -/
def optimum {n : ℕ} (p : Fin n → ℝ) : ℝ := sInf (Set.range (cost p))

def excess {n : ℕ} (p : Fin n → ℝ) (σ : ListState n) : ℝ := cost p σ - optimum p

/-- The source's decreasing relabeling, with ties allowed. -/
def Decreasing {n : ℕ} (p : Fin n → ℝ) : Prop := Antitone p

end TranspositionIID.Main


