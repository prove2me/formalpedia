-- Prove2me | Definitions.Def_SparseSDP_TwoSided_lanczosProg
-- name    : SparseSDP_TwoSided_lanczosProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:17.002968+00:00
-- url     : https://prove2.me/theorems/425d60e1-3e21-4ce8-b78e-e899915f0432
-- title:
--   Algorithm 4: Lánczos approximation of $e^Ku$, as a charged program
-- statement:
--   **Algorithm 4** (p. 25). From $q_1=u/\|u\|_2$, $\beta_0=0$, for $j=1,\dots,k$:
--   $$
--   w\leftarrow Kq_j-\beta_{j-1}q_{j-1},\quad \alpha_j\leftarrow q_j^\dagger w,\quad w\leftarrow w-\alpha_jq_j,\quad \beta_j\leftarrow\|w\|_2,
--   $$
--   stopping with $\ell=j$ if $\beta_j=0$ and otherwise setting $q_{j+1}=w/\beta_j$ for $j<k$. With $T_\ell$ the tridiagonal matrix of the $\alpha_j,\beta_j$, the return value is $\|u\|_2Q_\ell e^{T_\ell}e_1$.
--
--   `lanczosCore` is the loop, `lanczosProg` the whole algorithm, with the product by $K$ supplied as a charged procedure so that its cost lands where the paper puts it. `lanczosExp K u k` is $\text{LánczosExp}(K,u,k)$ of Eq. (85).
--
--   The two primitives `tridiagExpE1` and `tridiagLamMax` return $e^{T_\ell}e_1$ and $\lambda_{\max}(T_\ell)$ exactly, at charge $\ell^2$. Neither is a finite arithmetic computation; they are the only matrix-function primitives of the model, and the paper's accounting assumes them (p. 27 for the first; Lemma 2.5, p. 21, for the second).
--
--   **Formalization Note** Rows of the proof are the 1-indexed $j$ of the page: the Lean loop variable is $j-1$.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Algorithm 4, p. 25; Eq. (85), p. 25; p. 27

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_RowAccess

open Matrix

namespace SparseSDP.TwoSided

variable {d : ℕ}

/-- The tridiagonal `T_ℓ` of Algorithm 4, line 14 (p. 25): `(T_ℓ)_{j,j} = αⱼ` and
`(T_ℓ)_{j,j+1} = (T_ℓ)_{j+1,j} = βⱼ`, with `ℓ = α.length`. -/
def tridiag (α β : List ℝ) : Matrix (Fin α.length) (Fin α.length) ℝ :=
  fun i j =>
    if i = j then α.getD i.val 0
    else if i.val + 1 = j.val then β.getD i.val 0
    else if j.val + 1 = i.val then β.getD j.val 0
    else 0

/-- Primitive: `e^{T_ℓ} e₁`, exactly, charged `ℓ²` ("the exponential of the tridiagonal compression",
p. 27). -/
noncomputable def tridiagExpE1 (α β : List ℝ) : Prog (Fin α.length → ℝ) :=
  op (α.length ^ 2) (NormedSpace.exp (tridiag α β) *ᵥ fun i => if i.val = 0 then 1 else 0)

/-- Primitive: the Ritz value `λmax(T_ℓ)`, exactly, charged `ℓ²` (Lemma 2.5, p. 21). -/
noncomputable def tridiagLamMax (α β : List ℝ) : Prog ℝ :=
  op (α.length ^ 2) (lamMax (tridiag α β))

/-- The output of the Lánczos loop: the basis `q₁, …, q_ℓ` and the coefficients of `T_ℓ`. -/
structure Krylov (d : ℕ) where
  /-- The basis `q₁, …, q_ℓ`. -/
  q : List (Vec d)
  /-- `α₁, …, α_ℓ`. -/
  α : List ℝ
  /-- `β₁, …, β_{ℓ−1}`. -/
  β : List ℝ

/-- Algorithm 4, lines 1–12 (p. 25), with the charged product `mv` in place of `K`. The loop stops
early when `βⱼ = 0`, so then `ℓ = j`; otherwise `ℓ = k`. -/
noncomputable def lanczosCore (mv : Vec d → Prog (Vec d)) (u : Vec d) (k : ℕ) :
    Prog (Krylov d) := do
  let nu ← nrm u
  let inv ← op 1 (1 / nu)
  let q1 ← scale inv u
  let mut qPrev : Vec d := 0
  let mut q : Vec d := q1
  let mut βPrev : ℝ := 0
  let mut Qs : List (Vec d) := []
  let mut αs : List ℝ := []
  let mut βs : List ℝ := []
  for j in List.range k do
    tick 1
    let Kq ← mv q
    let w ← axpy (-βPrev) qPrev Kq
    let a ← dotp q w
    let w' ← axpy (-a) q w
    let b ← nrm w'
    tick 2
    Qs := Qs ++ [q]
    αs := αs ++ [a]
    tick 1
    if b = 0 then
      break
    tick 1
    if j + 1 < k then
      tick 1
      βs := βs ++ [b]
      let binv ← op 1 (1 / b)
      let qNext ← scale binv w'
      qPrev := q
      q := qNext
      βPrev := b
  pure ⟨Qs, αs, βs⟩

/-- Algorithm 4 (p. 25): `‖u‖₂ Q_ℓ e^{T_ℓ} e₁`, with the charged product `mv`. -/
noncomputable def lanczosProg (mv : Vec d → Prog (Vec d)) (u : Vec d) (k : ℕ) :
    Prog (Vec d) := do
  let kr ← lanczosCore mv u k
  let c ← tridiagExpE1 kr.α kr.β
  let mut y : Vec d := 0
  for p in kr.q.zip (List.ofFn c) do
    tick 1
    y ← axpy p.2 p.1 y
  let nu ← nrm u
  scale nu y

/-- `LánczosExp(K, u, k)` of Eq. (85), p. 25: the value of Algorithm 4 with the product by `K`.

**Formalization Note.** The program draws nothing, so the value does not depend on the tape. -/
noncomputable def lanczosExp (K : Mat d) (u : Vec d) (k : ℕ) : Vec d :=
  runVal (lanczosProg (fun v => pure (K *ᵥ v)) u k) fun _ => (0, 0)

end SparseSDP.TwoSided


