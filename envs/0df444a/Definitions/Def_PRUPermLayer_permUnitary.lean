-- Prove2me | Definitions.Def_PRUPermLayer_permUnitary
-- name    : PRUPermLayer_permUnitary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:47.45123+00:00
-- url     : https://prove2.me/theorems/06f078da-fa87-4c85-a4a1-03f836b93d6f
-- title:
--   Permutation unitary $P_\sigma|x\rangle = |\sigma(x)\rangle$
-- statement:
--   Identify $[N]$ with $\{0,1\}^n$, $N = 2^n$. For a permutation $\sigma$ of $[N]$, the **permutation unitary** $P_\sigma$ is defined by
--   $$
--   P_\sigma |x\rangle = |\sigma(x)\rangle \qquad (x \in [N]).
--   $$
--   Its matrix has entry $1$ in row $\sigma(y)$ of column $y$ and $0$ elsewhere.
--
--   A uniformly random $P_\sigma$ is the classical half of the construction $PL$.
--
--   **Formalization Note** The direction is the printed one: column $y$ is $|\sigma(y)\rangle$. (Mathlib's permutation matrix of $\sigma$ is the transpose.)
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8 (PDF p.10)

import Mathlib

namespace PRUPermLayer

/-- The permutation unitary `P_σ` of a permutation `σ` of `[N]`, `N = 2ⁿ`, defined by
`P_σ|x⟩ = |σ(x)⟩` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8 (PDF p.10)). Its `(x, y)` entry is `1` if `x = σ y` and `0`
otherwise, so column `y` is the basis vector `|σ y⟩`.

**Formalization Note** Mathlib's `Equiv.Perm.permMatrix σ` is the transpose of this matrix and is
not used. The unitarity proof is part of the definition. -/
noncomputable def permUnitary {n : ℕ} (σ : Equiv.Perm (Fin (2 ^ n))) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  ⟨Matrix.of fun x y => if x = σ y then 1 else 0, by
    rw [Matrix.mem_unitaryGroup_iff']
    ext y z
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.of_apply, Matrix.one_apply]
    simp [apply_ite star, Finset.sum_ite_eq', σ.injective.eq_iff, eq_comm]⟩

end PRUPermLayer


