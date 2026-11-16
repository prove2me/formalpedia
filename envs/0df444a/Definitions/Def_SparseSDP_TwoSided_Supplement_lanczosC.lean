-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Supplement_lanczosC
-- name    : SparseSDP_TwoSided_Supplement_lanczosC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:31:25.973095+00:00
-- url     : https://prove2.me/theorems/02653b95-9a42-4204-a868-3daf601eee79
-- title:
--   Algorithm 4 over $\mathbb C$ (the Haar-random Lánczos run of Proposition 4.3) as a charged program
-- statement:
--   Algorithm 4 run on complex vectors: from a nonzero $u\in\mathbb C^n$ and a charged product $v\mapsto Kv$ with a Hermitian $K$, it builds $q_1=u/\|u\|_2$ and, for $j=1,\dots,k$, $w=Kq_j-\beta_{j-1}q_{j-1}$, $\alpha_j=q_j^\dagger w$, $w\leftarrow w-\alpha_jq_j$, $\beta_j=\|w\|_2$, stopping with $\ell=j$ if $\beta_j=0$, else $q_{j+1}=w/\beta_j$. With the tridiagonal $T_\ell$ ($(T_\ell)_{jj}=\alpha_j$, $(T_\ell)_{j,j+1}=(T_\ell)_{j+1,j}=\beta_j$) it returns
--   $$
--   \mathrm{L\acute anczosExp}(K,u,k)=\|u\|_2\,Q_\ell e^{T_\ell}e_1 .
--   $$
--   The exponential of $T_\ell$ is the published exact primitive charged $\ell^2$.
--
--   This is the computation of Proposition 4.3, used in Algorithm 5 with $K=-H/2$ to approximate $e^{-H/2}u$.
--
--   **Formalization Note** For Hermitian $K$, $\alpha_j=q_j^\dagger w$ is real in exact arithmetic; the program stores its real part, so $T_\ell$ is the real symmetric matrix of line 14.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Algorithm 4, p. 25; Eq. (85); Proposition 4.3, p. 26

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_lanczosProg
import Definitions.Def_SparseSDP_TwoSided_Supplement_cvec

open Matrix

namespace SparseSDP.TwoSided.Supplement

open SparseSDP.TwoSided

variable {d : ℕ}

/-- The output of the complex Lánczos loop: the basis `q₁, …, q_ℓ` and the coefficients of `T_ℓ`. -/
structure CKrylov (d : ℕ) where
  /-- The basis `q₁, …, q_ℓ`. -/
  q : List (CVec d)
  /-- `α₁, …, α_ℓ`. -/
  α : List ℝ
  /-- `β₁, …, β_{ℓ−1}`. -/
  β : List ℝ

/-- Algorithm 4, lines 1–12 (p. 25), over `ℂ`, with the charged product `mv` in place of `K`
(the run of Proposition 4.3, p. 26). The loop stops early when `βⱼ = 0`, so then `ℓ = j`.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Algorithm 4, p. 25; Proposition 4.3, p. 26.

**Formalization Note.** Line 5 sets `αⱼ ← qⱼ†w`. For Hermitian `K` this number is real in exact
arithmetic (`qⱼ†Kqⱼ` is real and `qⱼ ⊥ qⱼ₋₁`), and the loop stores its real part, so `T_ℓ` is the
real symmetric tridiagonal matrix of line 14 and the published primitive `tridiagExpE1` applies. -/
noncomputable def lanczosCoreC (mv : CVec d → Prog (CVec d)) (u : CVec d) (k : ℕ) :
    Prog (CKrylov d) := do
  let nu ← cnrm u
  let inv ← op 1 (1 / nu)
  let q1 ← cscale inv u
  let mut qPrev : CVec d := 0
  let mut q : CVec d := q1
  let mut βPrev : ℝ := 0
  let mut Qs : List (CVec d) := []
  let mut αs : List ℝ := []
  let mut βs : List ℝ := []
  for j in List.range k do
    tick 1
    let Kq ← mv q
    let w ← caxpy (-(βPrev : ℂ)) qPrev Kq
    let a ← cdotp q w
    let w' ← caxpy (-((a.re : ℝ) : ℂ)) q w
    let b ← cnrm w'
    tick 2
    Qs := Qs ++ [q]
    αs := αs ++ [a.re]
    tick 1
    if b = 0 then
      break
    tick 1
    if j + 1 < k then
      tick 1
      βs := βs ++ [b]
      let binv ← op 1 (1 / b)
      let qNext ← cscale binv w'
      qPrev := q
      q := qNext
      βPrev := b
  pure ⟨Qs, αs, βs⟩

/-- Algorithm 4 over `ℂ` (p. 25): `‖u‖₂ Q_ℓ e^{T_ℓ} e₁`, with the charged product `mv` and the
published tridiagonal primitive `tridiagExpE1` (charged `ℓ²`). -/
noncomputable def lanczosProgC (mv : CVec d → Prog (CVec d)) (u : CVec d) (k : ℕ) :
    Prog (CVec d) := do
  let kr ← lanczosCoreC mv u k
  let c ← tridiagExpE1 kr.α kr.β
  let mut y : CVec d := 0
  for p in kr.q.zip (List.ofFn c) do
    tick 1
    y ← caxpy (p.2 : ℂ) p.1 y
  let nu ← cnrm u
  cscale nu y

end SparseSDP.TwoSided.Supplement


