-- Prove2me | Definitions.Def_HSElemKernel_PhiVar
-- name    : HSElemKernel_PhiVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:26:31.057826+00:00
-- url     : https://prove2.me/theorems/908282f0-3ed4-4489-89ac-0e3d7484e2a9
-- title:
--   Variables of $\Phi_{\mathcal F}$ (Table 2)
-- statement:
--   The variables of the formula $\Phi_{\mathcal F}$ (for an instance, a set $X \subseteq U$, a pair $\mathcal F$, an address length $\ell$ and a cardinality encoder $E$) form eight disjoint blocks:
--
--   1. $s_x$, $x \in X$: whether $x$ is selected;
--   2. $w_{c,r}$, $(c, r) \in [B] \times [t]$: whether bucket $c$ uses $g_r$;
--   3. $a_{c,j}$, $(c, j) \in [B] \times [q_2]$: whether subbucket $(c, j)$ is active;
--   4. $z_{c,j,\beta}$, $(c, j, \beta) \in [B] \times [q_2] \times [\ell]$: bit $\beta$ of the address stored in $(c, j)$;
--   5. $p_{c,r,j}$, $(c, r, j) \in [B] \times [t] \times [q_2]$, of (7);
--   6. $p^0_{c,r,j,\beta}$ and $p^1_{c,r,j,\beta}$ of (8);
--   7. for each bucket $c$, the auxiliary variables of $E$'s encoding of $\sum_r w_{c,r} = 1$ (5);
--   8. the auxiliary variables of $E$'s encoding of $\sum_x s_x + \sum_{c,j} a_{c,j} \le k$ (6).
--
--   The number $N$ of variables of $\Phi_{\mathcal F}$ is the number of elements of this set.
--
--   **Formalization Note** Each cardinality constraint has its own fresh auxiliary variables.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Table 2, p.11, and Eqs. (5)–(8), pp.11–12

import Mathlib
import Definitions.Def_HSElemKernel_CardEncoder
import Definitions.Def_HSElemKernel_TwoLevelHash

namespace HSElemKernel

/-- The variables of the formula `Φ_F` (Sheng–Xiao, arXiv:2609.06512, held version sha256
aca9c70e…, Table 2, p.11, Eqs. (5)–(8), pp.11–12), as a sum of eight blocks:
1. `s_x`, `x ∈ X`;
2. `w_{c,r}`, `(c, r) ∈ [B] × [t]`;
3. `a_{c,j}`, `(c, j) ∈ [B] × [q₂]`;
4. `z_{c,j,β}`, `(c, j, β) ∈ [B] × [q₂] × [ℓ]`;
5. `p_{c,r,j}` of (7);
6. `p^b_{c,r,j,β}` of (8), `b ∈ {0, 1}`;
7. for each bucket `c`, the auxiliary variables of the encoding of `∑_r w_{c,r} = 1` (5);
8. the auxiliary variables of the encoding of `∑_x s_x + ∑_{c,j} a_{c,j} ≤ k` (6).

**Formalization Note** The number `N` of variables of `Φ_F` is `Fintype.card` of this type.
Each cardinality constraint has its own fresh auxiliary variables (blocks 7 and 8); the sums are
encoded by the encoder `E`. The accessors `vS`, …, `vAux6` name the blocks. -/
abbrev PhiVar {n : ℕ} (E : CardEncoder) (X : Finset (Fin n)) (F : TwoLevelHash (Fin n))
    (ℓ k : ℕ) : Type :=
  {x // x ∈ X} ⊕ (Fin F.B × Fin F.t) ⊕ (Fin F.B × Fin F.q2) ⊕ (Fin F.B × Fin F.q2 × Fin ℓ) ⊕
    (Fin F.B × Fin F.t × Fin F.q2) ⊕ (Fin F.B × Fin F.t × Fin F.q2 × Fin ℓ × Bool) ⊕
    (Fin F.B × Fin (E.aux F.t 1 .eq)) ⊕ Fin (E.aux (X.card + F.B * F.q2) k .le)

section accessors
variable {n : ℕ} {E : CardEncoder} {X : Finset (Fin n)} {F : TwoLevelHash (Fin n)} {ℓ k : ℕ}

/-- `s_x` -/
def PhiVar.vS (x : {x // x ∈ X}) : PhiVar E X F ℓ k := Sum.inl x
/-- `w_{c,r}` -/
def PhiVar.vW (c : Fin F.B) (r : Fin F.t) : PhiVar E X F ℓ k := Sum.inr (Sum.inl (c, r))
/-- `a_{c,j}` -/
def PhiVar.vA (c : Fin F.B) (j : Fin F.q2) : PhiVar E X F ℓ k :=
  Sum.inr (Sum.inr (Sum.inl (c, j)))
/-- `z_{c,j,β}` -/
def PhiVar.vZ (c : Fin F.B) (j : Fin F.q2) (β : Fin ℓ) : PhiVar E X F ℓ k :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, j, β))))
/-- `p_{c,r,j}` -/
def PhiVar.vP (c : Fin F.B) (r : Fin F.t) (j : Fin F.q2) : PhiVar E X F ℓ k :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, r, j)))))
/-- `p^b_{c,r,j,β}` -/
def PhiVar.vPb (c : Fin F.B) (r : Fin F.t) (j : Fin F.q2) (β : Fin ℓ) (b : Bool) :
    PhiVar E X F ℓ k :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, r, j, β, b))))))
/-- the auxiliary variables of the encoding of (5) for bucket `c` -/
def PhiVar.vAux5 (c : Fin F.B) (i : Fin (E.aux F.t 1 .eq)) : PhiVar E X F ℓ k :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, i)))))))
/-- the auxiliary variables of the encoding of (6) -/
def PhiVar.vAux6 (i : Fin (E.aux (X.card + F.B * F.q2) k .le)) : PhiVar E X F ℓ k :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))))

end accessors

end HSElemKernel


