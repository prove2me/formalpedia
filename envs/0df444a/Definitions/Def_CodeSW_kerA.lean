-- Prove2me | Definitions.Def_CodeSW_kerA
-- name    : CodeSW_kerA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:22.368303+00:00
-- url     : https://prove2.me/theorems/d9d388b4-4ad7-4766-861e-c1634703c344
-- title:
--   The code $X(A)=\ker(h_A)$, its dimension $k(A)$, satisfied checks $E(x)$, Hamming weight, indicator vectors
-- statement:
--   Let $h\in\{0,1\}^{c\times n}$ be a parity check matrix over $\mathbb F_2$, with configurations $X=\{0,1\}^n$ and (indices of) checks $E=[c]$. This module fixes the basic vocabulary of the code.
--
--   1. The **Hamming weight** $|v|$ of a binary vector is its number of nonzero coordinates.
--   2. The **satisfied checks** of $x\in X$ are $E(x):=E\setminus\mathrm{supp}(hx)$.
--   3. For $A\subseteq E$, $h_A$ is the row-submatrix of $h$ indexed by $A$, and $X(A):=\ker(h_A)$ is the set of configurations satisfying every check in $A$. Its dimension over $\mathbb F_2$ is $k(A)$, so $|\ker(h_A)|=2^{k(A)}$.
--   4. The **indicator vector** $1_A\in\{0,1\}^c$ of $A\subseteq E$ has support exactly $A$.
--
--   All later objects of the mission (the Gibbs law, the Code Swendsen-Wang chain, the random cluster model and the even cover model) are written in these terms.
--
--   **Formalization Note** $\mathbb F_2$ is `ZMod 2`, checks are `Fin c`, and sets of checks are `Finset (Fin c)`.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), §2.1.2, eq. (4), p.11; §3.2, p.16; §3.3.2, p.20; Appendix A, p.34

import Mathlib
open Matrix
noncomputable section

namespace CodeSW

/-- The **Hamming weight** `|v| = #{i : v_i ≠ 0}` of a binary vector `v ∈ {0,1}^k`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, §2.1.2, eq. (4), p.11: "|x| = ∑_i x_i is the Hamming weight of x").

**Formalization Note** `F₂ = ZMod 2`; for a 0/1 vector the number of nonzero coordinates is the
integer sum `∑_i x_i` of the page. -/
def hammingWeight {ι : Type*} [Fintype ι] (v : ι → ZMod 2) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ 0).card

/-- The set of **satisfied checks** `E(x) := E \ supp(hx)` of a configuration `x ∈ {0,1}^n` for the
parity check matrix `h ∈ {0,1}^{c×n}`, with checks `E = [c]`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §3.2, p.16).

**Formalization Note** Checks are indexed by `Fin c`; a set of checks is a `Finset (Fin c)`. -/
def satChecks {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    Finset (Fin c) :=
  Finset.univ.filter fun e => (h *ᵥ x) e = 0

/-- `X(A) := ker(h_A)`, the code of the row-submatrix `h_A` of `h` indexed by a set of checks
`A ⊆ E`: the configurations `x` satisfying every check of `A`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §3.2, p.16, and Appendix A, p.34).

**Formalization Note** `h_A` is `h.submatrix (↑) id` on the subtype of `A`; `x ∈ kerA h A` iff
`(h x)_e = 0` for every `e ∈ A`. For `A = E` this is the code `C_h = ker h` (§2.1.1, p.10). -/
def kerA {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (A : Finset (Fin c)) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  LinearMap.ker (h.submatrix (fun e : A => (e : Fin c)) id).mulVecLin

/-- `k(A)`, the dimension of `ker(h_A)` over `F₂` (arXiv:2510.08446, manuscript sha256 4e4abb5e…,
§3.2, p.16: "where k(A) is the dimension of ker(h_A)"). Hence `|ker h_A| = 2^{k(A)}`. -/
def kDim {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (A : Finset (Fin c)) : ℕ :=
  Module.finrank (ZMod 2) (kerA h A)

/-- The binary indicator vector `1_A ∈ {0,1}^c` of a set of checks `A ⊆ E`, with `supp(1_A) = A`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §3.3.2, p.20). -/
def ind {c : ℕ} (A : Finset (Fin c)) : Fin c → ZMod 2 :=
  fun e => if e ∈ A then 1 else 0

end CodeSW


