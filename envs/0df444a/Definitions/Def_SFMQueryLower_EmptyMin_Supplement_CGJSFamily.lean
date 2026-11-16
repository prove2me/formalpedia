-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_Supplement_CGJSFamily
-- name    : SFMQueryLower_EmptyMin_Supplement_CGJSFamily
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:26:28.734861+00:00
-- url     : https://prove2.me/theorems/000f1f52-73b8-4238-9ca5-37d6b9c1353a
-- title:
--   The CGJS family $\mathcal F$ of layered submodular functions on $[2k]$
-- statement:
--   Let $k$ be a positive integer, $n=2k$, and let $\pi$ be a permutation of $[n]$, read as the list $\pi(1),\dots,\pi(n)$. For each layer $i\in[k]$ put
--   $$p_i^\pi:=\pi(2i-1),\qquad r_i^\pi:=\pi(2i),\qquad A_i^\pi:=\{p_i^\pi,r_i^\pi\},$$
--   and let $V_0^\pi:=\varnothing$ and $V_i^\pi:=\{\pi(1),\dots,\pi(2i)\}$. Set $h_0^\pi(\varnothing):=0$ and, for $i\in[k]$ and $S\subseteq V_i^\pi$,
--   $$h_i^\pi(S):=\begin{cases}\dfrac{h_{i-1}^\pi(S\setminus A_i^\pi)}{16i}, & S\cap A_i^\pi=\{p_i^\pi\},\\[4pt] 1+\dfrac{|S\setminus A_i^\pi|}{4i}, & S\cap A_i^\pi=\varnothing,\\[4pt] 1-\dfrac{|S\setminus A_i^\pi|}{4i}, & S\cap A_i^\pi=A_i^\pi,\\[4pt] 2, & S\cap A_i^\pi=\{r_i^\pi\}.\end{cases}$$
--   The CGJS family $\mathcal F$ consists of the functions $h_k^\pi:2^{[n]}\to\mathbb R$ over all permutations $\pi$. The set $P^\pi:=\{\pi(1),\pi(3),\dots,\pi(2k-1)\}=\{p_1^\pi,\dots,p_k^\pi\}$ is the unique set that passes every layer.
--
--   This family, an equivalent re-indexing of the construction of Chakrabarty, Graur, Jiang and Sidford with $r=1$, is the input class of the $\Theta(n\log\log n)$ randomized bounds of Appendix C.
--
--   **Formalization Note** The ground set is `Fin (2 * k)` and positions of $\pi$ are 0-based: source position $2i-1$ (resp. $2i$) is 0-based position $2(i-1)$ (resp. $2(i-1)+1$), given by `pairEquiv k (i-1, false)` (resp. `true`). `cgjsAux π i S` is $h_i^\pi(S\cap V_i^\pi)$: reading an arbitrary set through its intersection with $V_i^\pi$ agrees with $h_i^\pi$ on subsets of $V_i^\pi$, and $V_k^\pi=[n]$, so `cgjsFunction π` is exactly $h_k^\pi$. The four cases are exhaustive because $p_i^\pi\ne r_i^\pi$; the final branch is the case $\{r_i^\pi\}$. The denominators use the layer index $i$, not $|V_i^\pi|$.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Definition C.1 and equation (13), printed p. 20 / PDF p. 21

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false

namespace SFMQueryLower.EmptyMin.Supplement

/-- 0-based pairing of `Fin (2 * k)`: `(a, false) ↦ 2a` and `(a, true) ↦ 2a + 1`.
The source's 1-based positions `2i − 1` and `2i` (layer `i = a + 1`) are the 0-based
positions `2a` and `2a + 1`. -/
def pairEquiv (k : ℕ) : Fin k × Bool ≃ Fin (2 * k) where
  toFun x := ⟨2 * x.1.val + (if x.2 then 1 else 0), by
    rcases x with ⟨a, b⟩
    have := a.isLt
    cases b <;> (simp; try omega)⟩
  invFun m := (⟨m.val / 2, by omega⟩, decide (m.val % 2 = 1))
  left_inv := by
    rintro ⟨a, b⟩
    cases b <;> refine Prod.ext (Fin.ext ?_) ?_ <;> (simp; try omega)
  right_inv := by
    intro m
    apply Fin.ext
    by_cases h : m.val % 2 = 1 <;> simp [h] <;> omega

@[simp] theorem pairEquiv_val (k : ℕ) (a : Fin k) (b : Bool) :
    (pairEquiv k (a, b)).val = 2 * a.val + (if b then 1 else 0) := rfl

/-- Definition C.1 (0-based layer `l`, source layer `i = l + 1`): `p_i = π(2i − 1)`. -/
def cgjsP {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) (l : Fin k) : Fin (2 * k) :=
  π (pairEquiv k (l, false))

/-- Definition C.1: `r_i = π(2i)`. -/
def cgjsR {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) (l : Fin k) : Fin (2 * k) :=
  π (pairEquiv k (l, true))

/-- Definition C.1: `A_i = {p_i, r_i}`. -/
def cgjsA {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) (l : Fin k) : Finset (Fin (2 * k)) :=
  {cgjsP π l, cgjsR π l}

/-- Definition C.1: `V_i = {π(1), …, π(2i)}` (source 1-based positions), i.e. the images of
the 0-based positions `< 2i`; `V_0 = ∅` and `V_k` is the whole ground set. -/
def cgjsV {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) (i : ℕ) : Finset (Fin (2 * k)) :=
  (Finset.univ.filter (fun m : Fin (2 * k) => m.val < 2 * i)).image π

/-- Definition C.1, recurrence (13). `cgjsAux π i S` is `h_i^π(S ∩ V_i^π)`; the source's
`h_i^π` is defined on subsets of `V_i^π`, and reading an arbitrary `S` through `S ∩ V_i^π`
agrees with it there. `h_0^π(∅) = 0`. For source layer `i + 1` (0-based layer `i`), with
`T = S ∩ V_{i+1}` and `A = A_{i+1}`, the four cases are `T ∩ A = {p}`, `∅`, `A`, `{r}`;
since `p ≠ r` they are exhaustive, so the last branch is exactly the case `T ∩ A = {r}`.
The denominators are `16 (i+1)` and `4 (i+1)`, with `i + 1` the source layer index. -/
noncomputable def cgjsAux {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) :
    ℕ → Finset (Fin (2 * k)) → ℝ
  | 0, _ => 0
  | i + 1, S =>
    if hi : i < k then
      let l : Fin k := ⟨i, hi⟩
      let A := cgjsA π l
      let T := S ∩ cgjsV π (i + 1)
      if T ∩ A = {cgjsP π l} then
        cgjsAux π i (T \ A) / (16 * ((i : ℝ) + 1))
      else if T ∩ A = ∅ then
        1 + ((T \ A).card : ℝ) / (4 * ((i : ℝ) + 1))
      else if T ∩ A = A then
        1 - ((T \ A).card : ℝ) / (4 * ((i : ℝ) + 1))
      else 2
    else 0

/-- Definition C.1: the member `h_k^π` of the CGJS family `F` on the ground set `[2k]`. -/
noncomputable def cgjsFunction {k : ℕ} (π : Equiv.Perm (Fin (2 * k)))
    (S : Finset (Fin (2 * k))) : ℝ :=
  cgjsAux π k S

/-- `P^π = {π(1), π(3), …, π(2k − 1)} = {p_1^π, …, p_k^π}`. -/
def cgjsMinimizer {k : ℕ} (π : Equiv.Perm (Fin (2 * k))) : Finset (Fin (2 * k)) :=
  Finset.univ.image (cgjsP π)

end SFMQueryLower.EmptyMin.Supplement


