-- Prove2me | Definitions.Def_LovaszSchrijver_OddHole_AlternatingWalk
-- name    : LovaszSchrijver_OddHole_AlternatingWalk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:46:27.842466+00:00
-- url     : https://prove2.me/theorems/2612e10a-ff3b-484c-8788-a56a768f5e3c
-- title:
--   Walks and the alternating sums b(v₀v₁) − a(v₁v₂) + ⋯ of Lemma 2.4
-- statement:
--   Let $H = (W, F)$ be a graph and let $a, b$ assign real values to edges. A sequence of (not necessarily distinct) vertices $v_0, v_1, \dots, v_p$ is a **walk** if $v_t$ and $v_{t+1}$ are adjacent for every $0 \le t < p$. Along such a walk, Lemma 2.4 (p. 178) uses two alternating sums:
--   $$\mathrm{alt}_b(v) = b(v_0v_1) - a(v_1v_2) + b(v_2v_3) - \cdots, \qquad \mathrm{alt}_a(v) = -a(v_0v_1) + b(v_1v_2) - a(v_2v_3) + \cdots,$$
--   where the $t$-th edge $v_tv_{t+1}$ ($t = 0, \dots, p-1$) enters $\mathrm{alt}_b$ as $+b(v_tv_{t+1})$ if $t$ is even and as $-a(v_tv_{t+1})$ if $t$ is odd, and enters $\mathrm{alt}_a$ with the opposite pattern. The empty walk ($p = 0$) has both sums equal to $0$.
--
--   **Formalization Note** A walk is a map $v : \{0, \dots, p\} \to W$; edge values are functions on unordered pairs (`Sym2 W`), so $a(v_tv_{t+1}) = a(v_{t+1}v_t)$ automatically.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 178, Lemma 2.4

import Mathlib

namespace LovaszSchrijver.OddHole

/-- `v₀, v₁, …, v_p` is a walk in `H`: consecutive vertices are adjacent. -/
def IsWalkSeq {W : Type} (H : SimpleGraph W) {p : ℕ} (v : Fin (p + 1) → W) : Prop :=
  ∀ t : Fin p, H.Adj (v t.castSucc) (v t.succ)

/-- The alternating sum `b(v₀v₁) − a(v₁v₂) + b(v₂v₃) − ⋯` along the walk (p. 178):
the `t`-th edge (counting from `0`) contributes `b` if `t` is even and `−a` if `t` is odd. -/
def altB {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 1) → W) : ℝ :=
  ∑ t : Fin p, if Even t.val then b s(v t.castSucc, v t.succ) else -a s(v t.castSucc, v t.succ)

/-- The alternating sum `−a(v₀v₁) + b(v₁v₂) − a(v₂v₃) + ⋯` along the walk (p. 178):
the `t`-th edge contributes `−a` if `t` is even and `b` if `t` is odd. -/
def altA {W : Type} (a b : Sym2 W → ℝ) {p : ℕ} (v : Fin (p + 1) → W) : ℝ :=
  ∑ t : Fin p, if Even t.val then -a s(v t.castSucc, v t.succ) else b s(v t.castSucc, v t.succ)

end LovaszSchrijver.OddHole


