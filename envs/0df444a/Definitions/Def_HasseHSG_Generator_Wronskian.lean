-- Prove2me | Definitions.Def_HasseHSG_Generator_Wronskian
-- name    : HasseHSG_Generator_Wronskian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:35:41.304512+00:00
-- url     : https://prove2.me/theorems/5ffaeb5e-3f28-42d2-a6bb-9ebc9847e8da
-- title:
--   The $D_{q,d}$-Wronskian and the Casoratian (Definition 6.1, Eqs. (16)–(17))
-- statement:
--   For a set $L$, a map $T:L\to L$ and $g_1,\dots,g_m\in L$, let $M_T(g_1,\dots,g_m)$ be the $m\times m$ matrix whose $(i,j)$ entry is $T^i(g_j)$, with rows $i=0,\dots,m-1$.
--
--   1. With $T=D_{q,d}$ on $L=\operatorname{Frac}(F(q)(t)[x])$ this is the **$D_{q,d}$-Wronskian matrix** of Eq. (16). Its determinant is the **Wronskian**
--   $$W_{D_{q,d}}(g_1,\dots,g_m)=\det\bigl[D_{q,d}^{\,i}(g_j)\bigr]_{0\le i<m,\;1\le j\le m}.$$
--   2. With $T=\sigma$ a field endomorphism, $M_\sigma$ is the **Casoratian** (p. 29). With $\sigma=\sigma_q$ on $L$ it is the matrix of Eq. (17).
--
--   The empty Wronskian ($m=0$) is $1$. The Wronskian is the tool that converts linear independence of a basis of the Hasse derivative space into a nonzero polynomial whose degree can be controlled.
--
--   **Formalization Note.** `iterMatrix T g` is the generic matrix. `wronskianMatrix a d g` and `wronskian a d g` use $D_{q,d}$ on $L$; `casoratiMatrix σ g` takes a ring endomorphism; `qCasoratiMatrix a g` uses $\sigma_q$ on $L$.
-- source:
--   Bal, Ghosh, Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary Characteristic Fields, STOC 2027 submission (held manuscript, sha256 1b7cccc3…), pp. 27–28, Definition 6.1, Eqs. (16)–(17); p. 29 (Casoratian of a difference field)

import Mathlib
import Definitions.Def_HasseHSG_Generator_QDifference

namespace HasseHSG.Generator

/-!
Bal, Ghosh, *Hitting Sets for Polynomials with Small Hasse Derivative Space over Arbitrary
Characteristic Fields*, §6: Definition 6.1 and Eq. (16) (p. 27), the Casoratian of Eq. (17)
(p. 28) and its version for a general difference field (p. 29).
-/

/-- The `m × m` matrix of iterates `(i, j) ↦ T^i (g_j)`, rows `i = 0, …, m − 1`. -/
def iterMatrix {L : Type*} {m : ℕ} (T : L → L) (g : Fin m → L) : Matrix (Fin m) (Fin m) L :=
  Matrix.of fun i j => T^[(i : ℕ)] (g j)

/-- The `D_{q,d}`-Wronskian matrix `M_{D_{q,d}}(g₁, …, g_m)` on `L` (Definition 6.1, Eq. (16)). -/
noncomputable def wronskianMatrix {F : Type*} [Field F] {n m : ℕ} (a : Fin n → F) (d : ℕ)
    (g : Fin m → LField F n) : Matrix (Fin m) (Fin m) (LField F n) :=
  iterMatrix (DqdL a d) g

/-- The `D_{q,d}`-Wronskian `W_{D_{q,d}}(g₁, …, g_m) = det M_{D_{q,d}}` (Definition 6.1). -/
noncomputable def wronskian {F : Type*} [Field F] {n m : ℕ} (a : Fin n → F) (d : ℕ)
    (g : Fin m → LField F n) : LField F n :=
  (wronskianMatrix a d g).det

/-- The Casoratian `M_σ(g₁, …, g_m)`, `(i, j) ↦ σ^i(g_j)`, for a field `L` with an endomorphism
`σ` (p. 29); with `σ = σ_q` on `L` it is Eq. (17). -/
def casoratiMatrix {L : Type*} [Field L] {m : ℕ} (σ : L →+* L) (g : Fin m → L) :
    Matrix (Fin m) (Fin m) L :=
  iterMatrix (⇑σ) g

/-- The Casoratian `M_{σ_q}(g₁, …, g_m)` on `L`, `(i, j) ↦ σ_q^i(g_j)` (Eq. (17)). -/
noncomputable def qCasoratiMatrix {F : Type*} [Field F] {n m : ℕ} (a : Fin n → F)
    (g : Fin m → LField F n) : Matrix (Fin m) (Fin m) (LField F n) :=
  iterMatrix (sigmaL a) g

end HasseHSG.Generator


