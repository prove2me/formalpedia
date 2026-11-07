-- Prove2me | Definitions.Def_CodeSW_metropolis
-- name    : CodeSW_metropolis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:26:50.223925+00:00
-- url     : https://prove2.me/theorems/f07b5a5c-963e-4cdd-98c9-cc603e77e9a3
-- title:
--   Lazy single-check Metropolis dynamics $P_{\mathrm{Metropolis}}$ and single-check dynamics $P_{\mathrm{SC}}$ of $\phi$
-- statement:
--   Two local chains on subsets of checks. The **lazy Metropolis dynamics** makes no change with probability $1/2$; otherwise it proposes $B=A\oplus e$ for a uniformly random check $e\in E$ and accepts with probability $\min\{1,\phi(B)/\phi(A)\}$:
--   $$P_{\mathrm{Metropolis}}(A,B)=\begin{cases}\frac1{2|E|}\min\{1,\phi(B)/\phi(A)\}&|A\oplus B|=1,\\[2pt] 1-\frac1{2|E|}\sum_{e\in E}\min\{1,\phi(A\oplus e)/\phi(A)\}&A=B,\\[2pt] 0&\text{else.}\end{cases}$$
--   The **lazy single-check dynamics** $P_{\mathrm{SC}}$ also stays with probability $1/2$. Otherwise it chooses a uniformly random check $e\in E$. If $k(A)=k(A\cup e)$ it moves to $A\cup e$ with probability $p$ and to $A\setminus e$ with probability $1-p$. If $k(A)\ne k(A\cup e)$ it moves to $A\cup e$ with probability $p/2$ and stays at $A$ with probability $1-p/2$.
--
--   The Metropolis chain carries the flow of Theorem 16, and the single-check chain is the one the operator identities of Lemma 29 express.
--
--   **Formalization Note** The rule of $P_{\mathrm{SC}}$ is read literally: for $e\in A$ we have $A\cup e=A$, so the first case applies. With no checks ($c=0$), Lean's $1/0=0$ makes $P_{\mathrm{Metropolis}}$ the identity on the single state $\emptyset$ and $P_{\mathrm{SC}}$ the junk matrix $I/2$; no statement of the mission uses the latter at $c=0$ beyond the identity of Lemma 29.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), §3.3.1, p.17; Appendix A, p.33

import Definitions.Def_CodeSW_rc
open Matrix
noncomputable section

namespace CodeSW

/-- The **lazy single-check Metropolis dynamics** of the random cluster model `ϕ` on subsets of
checks `Ω = 2^E`, `E = [c]`: with probability `1/2` nothing changes, otherwise `B = A ⊕ e` is
proposed for a uniformly random check `e` and accepted with probability `min{1, ϕ(B)/ϕ(A)}`:
`P(A,B) = (1/(2|E|)) min{1, ϕ(B)/ϕ(A)}` if `|A ⊕ B| = 1`,
`P(A,A) = 1 − (1/(2|E|)) ∑_{e∈E} min{1, ϕ(A⊕e)/ϕ(A)}`, and `0` otherwise
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, §3.3.1, p.17).

**Formalization Note** `A ⊕ e` is `symmDiff A {e}` and `|E| = c`. For `c = 0` Lean's `1/0 = 0`
makes this the identity on the single state `∅`, the only sensible chain there. -/
def metropolis {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) :
    Matrix (Finset (Fin c)) (Finset (Fin c)) ℝ :=
  fun A B =>
    if A = B then
      1 - (1 / (2 * (c : ℝ))) * ∑ e : Fin c, min 1 (rc h p (symmDiff A {e}) / rc h p A)
    else if (symmDiff A B).card = 1 then
      (1 / (2 * (c : ℝ))) * min 1 (rc h p B / rc h p A)
    else 0

/-- The **lazy single-check (SC) dynamics** of the random cluster model (arXiv:2510.08446,
manuscript sha256 4e4abb5e…, Appendix A, p.33):
1. with probability `1/2` let `B = A`;
2. otherwise choose a uniformly random check `e ∈ E`;
   if `k(A) = k(A ∪ e)`, let `B = A ∪ e` with probability `p` and `B = A \ e` with probability
   `1 − p`; if `k(A) ≠ k(A ∪ e)`, let `B = A ∪ e` with probability `p/2` and `B = A` with
   probability `1 − p/2`.

**Formalization Note** The rule is read literally: for `e ∈ A`, `A ∪ e = A`, so the first case
applies (stay with probability `p`, drop `e` with probability `1 − p`). `|E| = c`; for `c = 0`
step 2 has no check to choose and the matrix is `I/2` (Lean's `1/0 = 0`). -/
def singleCheck {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) :
    Matrix (Finset (Fin c)) (Finset (Fin c)) ℝ :=
  fun A B =>
    (1 / 2) * (if B = A then 1 else 0) + (1 / (2 * (c : ℝ))) * ∑ e : Fin c,
      if kDim h A = kDim h (insert e A) then
        p * (if B = insert e A then 1 else 0) + (1 - p) * (if B = A.erase e then 1 else 0)
      else
        (p / 2) * (if B = insert e A then 1 else 0) + (1 - p / 2) * (if B = A then 1 else 0)

end CodeSW


