-- Prove2me | Definitions.Def_SharpConsist_fA
-- name    : SharpConsist_fA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:28.248302+00:00
-- url     : https://prove2.me/theorems/f75954bb-6135-4e4a-97d5-1c529f895d13
-- title:
--   The hard instance $f_A$ of Eq. (5.9)
-- statement:
--   Let $X=[n]$, a set $A\subseteq X$ (a $k$-set in the paper, with $n=(m+1)k$) and $\bar A=X\setminus A$. For $U\subseteq X\cup\{r\}$ let $x=|U\cap A|/k$ and $y=|U\cap\bar A|/k$ (the final element $r$ is in neither count). The **hard instance** is
--   $$f_A(U)=\begin{cases}F_\delta(x,y),&r\notin U,\\ K_\delta(x,y),&r\in U.\end{cases}$$
--   Before $r$ arrives every query evaluates $F_\delta$, which is exactly $\psi(|S|/k)$ on balanced sets; the branch $K_\delta$ makes the hidden set $A$, together with $r$, valuable.
--
--   **Formalization Note.** $X\cup\{r\}$ is `Fin (n+1)` with $X$ the image of `Fin n` (0-based) and $r$ = `Fin.last n`. The definition is total in $n,k,A$; the statements about it assume $n=(m+1)k$, $k\ge1$ and $|A|=k$.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §5.2, Eq. (5.9), p.15

import Mathlib
import Definitions.Def_SharpConsist_Fdelta
import Definitions.Def_SharpConsist_embedX

namespace SharpConsist

/-- The **hard instance** of Eq. (5.9). Fu–Zhang–Tao, arXiv:2609.09986 (held version, sha256
874ec76c…), §5.2, p.15. For a hidden set `A ⊆ X = Fin n` and `U ⊆ X ∪ {r}`, with
`x = |U ∩ A|/k` and `y = |U ∩ Ā|/k` (the final element `r` is in neither count),
`f_A(U) = F_δ(x, y)` if `r ∉ U` and `f_A(U) = K_δ(x, y)` if `r ∈ U`.

**Formalization Note.** The ground set is `Fin (n+1)`, `X` is the image of `Fin n` under
`Fin.castSucc`, and `r = Fin.last n`. The paper's `X = [n] = {1, …, n}` is 0-based here. The definition
makes sense for every `n`, `k` and `A`; the statements about it assume `n = (m+1)k`, `1 ≤ k` and
`|A| = k`. -/
noncomputable def fA (T : ℝ) (m k : ℕ) {n : ℕ} (A : Finset (Fin n)) (U : Finset (Fin (n + 1))) : ℝ :=
  if Fin.last n ∈ U then
    Kdelta T m (((U ∩ embedX A).card : ℝ) / (k : ℝ)) (((U ∩ embedX Aᶜ).card : ℝ) / (k : ℝ))
  else
    Fdelta T m (((U ∩ embedX A).card : ℝ) / (k : ℝ)) (((U ∩ embedX Aᶜ).card : ℝ) / (k : ℝ))

end SharpConsist


