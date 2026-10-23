-- Prove2me | Definitions.Def_WalledBrauer_SuperSchurWeyl_TensorSpace
-- name    : WalledBrauer_SuperSchurWeyl_TensorSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:42.784947+00:00
-- url     : https://prove2.me/theorems/f99db8c6-9f4e-4191-a724-5b74f1ed5b9c
-- title:
--   gl(m|n) acting on V^{⊗r} ⊗ W^{⊗s} with the super sign rule, the super-commutant End_g, Ω_{a,b}, and flip_{r,s} on End (pp. 48–49, 54; (7.1)–(7.4), (7.16))
-- statement:
--   Fix integers $m, n \ge 0$ and let $V$ be the vector superspace with homogeneous basis $v_1, \dots, v_{m+n}$, where $|v_i| = |i| = 0$ for $i \le m$ and $|i| = 1$ for $i > m$. The general linear Lie superalgebra $\mathfrak g = \mathfrak{gl}_{m|n}(\mathbb C)$ is $\operatorname{End}(V)$; its matrix unit $e_{a,b}$ is homogeneous of parity $|a| + |b|$. Let $W = V^*$ with dual basis $w_1, \dots, w_{m+n}$. By (7.1) of the paper,
--
--   $$
--   e_{a,b} v_k = \delta_{b,k} v_a, \qquad e_{a,b} w_k = -\delta_{a,k} (-1)^{(|a|+|b|)|a|} w_b .
--   $$
--
--   **Tensor space.** For a pattern of $N$ tensor slots, each carrying $V$ or $W$, the tensor product has basis $u_{\mathbf i} = u_{i_1} \otimes \cdots \otimes u_{i_N}$ indexed by $\mathbf i \in I^N$, $I = \{1, \dots, m+n\}$, with $u = v$ in a $V$-slot and $u = w$ in a $W$-slot; $u_{\mathbf i}$ has parity $|\mathbf i| = |i_1| + \cdots + |i_N|$. The two cases used are $V^{\otimes N}$ and $V^{\otimes r} \otimes W^{\otimes s}$ ($N = r + s$, the first $r$ slots carry $V$). Operators are matrices $X$ with $X u_{\mathbf i} = \sum_{\mathbf j} X_{\mathbf j \mathbf i} u_{\mathbf j}$.
--
--   **The action of $\mathfrak g$.** The element $e_{a,b}$ acts through the coproduct $\Delta(x) = x \otimes 1 + 1 \otimes x$ and the sign rule $(a \otimes b)(c \otimes d) = (-1)^{|b||c|} ac \otimes bd$: it acts as $E_{a,b} = \sum_{c=1}^{N} E^{(c)}_{a,b}$, where the slot operator $E^{(c)}_{a,b}$ (the action of $1^{\otimes(c-1)} \otimes e_{a,b} \otimes 1^{\otimes(N-c)}$) is
--
--   $$
--   E^{(c)}_{a,b}\, u_{i_1} \otimes \cdots \otimes u_{i_N} = (-1)^{(|a|+|b|)(|i_1| + \cdots + |i_{c-1}|)}\, u_{i_1} \otimes \cdots \otimes (e_{a,b} u_{i_c}) \otimes \cdots \otimes u_{i_N}.
--   $$
--
--   **The super-commutant.** Following p. 49, $\mathfrak g$ acts on $\operatorname{End}$ of a supermodule by $(xf)(u) = x(f(u)) - (-1)^{|x||f|} f(xu)$ for homogeneous $x$ and $f$. Every operator splits as $X = X_0 + X_1$, with $X_0$ the entries $X_{\mathbf j \mathbf i}$ with $|\mathbf j| = |\mathbf i|$ and $X_1$ the others, so
--
--   $$
--   e_{a,b} \cdot X = E_{a,b} X - \bigl(X_0 E_{a,b} + (-1)^{|a|+|b|} X_1 E_{a,b}\bigr).
--   $$
--
--   $\operatorname{End}_{\mathfrak g}$ is the subspace of all (not necessarily homogeneous) operators $X$ annihilated by every $x \in \mathfrak g$; as the action is linear in $x$ and the $e_{a,b}$ span $\mathfrak g$, these are the $X$ with $e_{a,b} \cdot X = 0$ for all $a, b$.
--
--   **The operators $\Omega_{p,q}$** of (7.3): for slots $p < q$,
--   $\Omega_{p,q} = \sum_{c,d} (-1)^{|d|} E^{(p)}_{c,d} E^{(q)}_{d,c}$.
--
--   **The map $\mathrm{flip}_{r,s}$ of (7.16), in coordinates.** For $\mathbf a \in I^{r+s}$ write $\mathbf a = \mathbf a^{\mathrm L} \mathbf a^{\mathrm R}$ (first $r$ and last $s$ entries) and $p(\mathbf a^{\mathrm R}) = \sum_{r < k < l} |a_k||a_l|$ as in (7.4). Then $\mathrm{flip}_{r,s} : \operatorname{End}(V^{\otimes(r+s)}) \to \operatorname{End}(V^{\otimes r} \otimes W^{\otimes s})$ is
--
--   $$
--   (\mathrm{flip}_{r,s} X)_{\mathbf a \mathbf c} = (-1)^{(|\mathbf a^{\mathrm R}| + |\mathbf c^{\mathrm R}|)|\mathbf c^{\mathrm R}| + p(\mathbf a^{\mathrm R}) + p(\mathbf c^{\mathrm R})}\; X_{\mathbf a^{\mathrm L}\mathbf c^{\mathrm R},\ \mathbf c^{\mathrm L}\mathbf a^{\mathrm R}} :
--   $$
--
--   the matrix unit of $V^{\otimes(r+s)}$ sending $v_{\mathbf c^{\mathrm L}} \otimes v_{\mathbf a^{\mathrm R}}$ to $v_{\mathbf a^{\mathrm L}} \otimes v_{\mathbf c^{\mathrm R}}$ goes to that sign times the matrix unit sending $v_{\mathbf c^{\mathrm L}} \otimes w_{\mathbf c^{\mathrm R}}$ to $v_{\mathbf a^{\mathrm L}} \otimes w_{\mathbf a^{\mathrm R}}$. This is the paper's $f \otimes g \mapsto f \otimes g^*$ under the identifications (7.13), (7.15) and (7.18).
--
--   These objects are the representation-theoretic side of mixed Schur–Weyl duality: the walled Brauer algebra acts on $V^{\otimes r} \otimes W^{\otimes s}$ by elements of $\operatorname{End}_{\mathfrak g}$.
--
--   **Formalization Note** Colours and slots are 0-based: a colour is `c : Fin (m + n)`, odd iff `m ≤ c`. A slot pattern is `κ : Fin N → Bool` (`true` = $V$); `allV N` is $V^{\otimes N}$ and `mixed r s` is $V^{\otimes r} \otimes W^{\otimes s}$. Operators are `Matrix (Fin N → Fin (m + n)) (Fin N → Fin (m + n)) ℂ`, row = output, column = input. Signs are `sgn k = (-1)^k` with `k : ℕ`. `EndG` is the intersection of the kernels of the linear maps `adE κ a b` (the action of $e_{a,b}$ on $\operatorname{End}$), over all colours `a b`. The coordinate formulas for the slot action and for $\mathrm{flip}_{r,s}$ are not printed in the paper; they follow from pp. 48–49 and (7.13)–(7.18).
-- source:
--   Brundan and Stroppel, Gradings on walled Brauer algebras and Khovanov's arc algebra, arXiv:1107.0999v1, pp. 48–50, (7.1)–(7.4), and p. 54, (7.15)–(7.16), with (7.13) on p. 53 and (7.18) on p. 55

import Mathlib

namespace WalledBrauer.SuperSchurWeyl

/-! Tensor space for `gl_{m|n}(ℂ)` (Brundan–Stroppel, arXiv:1107.0999v1, pp. 48–50, 54).
Colours are `c : Fin (m + n)` (the paper's `1, …, m + n`, 0-based); `c` is odd iff `m ≤ c`.
A tensor slot pattern `κ : Fin N → Bool` says which of the `N` slots carry `V` (`true`) and
which carry `W = V*` (`false`). The basis vector indexed by `i : Fin N → Fin (m + n)` is
`u_{i 0} ⊗ ⋯ ⊗ u_{i (N-1)}` with `u = v` in a `V`-slot and `u = w` in a `W`-slot. Operators
are matrices whose column is the input basis vector: `X u_i = ∑_j X j i u_j`. -/

/-- The parity `|c| ∈ {0, 1}` of a colour (p. 48): `0` if `c < m`, `1` otherwise. -/
def par (m : ℕ) {n : ℕ} (c : Fin (m + n)) : ℕ := if c.val < m then 0 else 1

/-- The parity `|i| = |i_1| + ⋯ + |i_t|` of a multi-index (7.4), as a natural number
(only its value mod 2 matters). -/
def tpar (m : ℕ) {n t : ℕ} (i : Fin t → Fin (m + n)) : ℕ := ∑ a, par m (i a)

/-- The sign `(-1)^k`. -/
def sgn (k : ℕ) : ℂ := (-1) ^ k

/-- Basis indices of an `N`-fold tensor product of copies of `V` and `W`. -/
abbrev Idx (m n N : ℕ) := Fin N → Fin (m + n)

/-- Operators on an `N`-fold tensor product of copies of `V` and `W`, as matrices
(column = input basis vector). -/
abbrev Op (m n N : ℕ) := Matrix (Idx m n N) (Idx m n N) ℂ

/-- The matrix unit `e_{a,b}` acting on one tensor factor (7.1): on `V`,
`e_{a,b} v_k = δ_{b,k} v_a`; on `W`, `e_{a,b} w_k = -δ_{a,k} (-1)^{(|a|+|b|)|a|} w_b`.
Entry `(k', k)` is the coefficient of the basis vector `k'` in the image of the basis
vector `k`. -/
def unitOn (m n : ℕ) (isV : Bool) (a b : Fin (m + n)) : Matrix (Fin (m + n)) (Fin (m + n)) ℂ :=
  fun k' k =>
    if isV then (if k = b ∧ k' = a then 1 else 0)
    else (if k = a ∧ k' = b then -sgn ((par m a + par m b) * par m a) else 0)

/-- The operator `E^{(c)}_{a,b}` by which `1^{⊗ c} ⊗ e_{a,b} ⊗ 1^{⊗ (N - 1 - c)} ∈ U(g)^{⊗ N}`
acts on the tensor space, by the sign rule (p. 48):
`u_{i_0} ⊗ ⋯ ⊗ u_{i_{N-1}} ↦ (-1)^{(|a|+|b|)(|i_0| + ⋯ + |i_{c-1}|)}
u_{i_0} ⊗ ⋯ ⊗ e_{a,b} u_{i_c} ⊗ ⋯ ⊗ u_{i_{N-1}}`. -/
def slotOp (m n : ℕ) {N : ℕ} (κ : Fin N → Bool) (c : Fin N) (a b : Fin (m + n)) : Op m n N :=
  fun j i =>
    if ∀ d, d ≠ c → j d = i d then
      sgn ((par m a + par m b) * ∑ d ∈ Finset.univ.filter (fun d : Fin N => d < c), par m (i d)) *
        unitOn m n (κ c) a b (j c) (i c)
    else 0

/-- The action of the matrix unit `e_{a,b} ∈ g = gl_{m|n}(ℂ)` on the tensor space, through
the iterated coproduct `Δ(x) = x ⊗ 1 + 1 ⊗ x` and the sign rule:
`E_{a,b} = ∑_c E^{(c)}_{a,b}`. -/
def actE (m n : ℕ) {N : ℕ} (κ : Fin N → Bool) (a b : Fin (m + n)) : Op m n N :=
  ∑ c, slotOp m n κ c a b

/-- The even part `X_0` of an operator: the entries `X j i` with `|j| ≡ |i| (mod 2)`. -/
def evenPart (m n : ℕ) {N : ℕ} (X : Op m n N) : Op m n N :=
  fun j i => if tpar m j % 2 = tpar m i % 2 then X j i else 0

/-- The odd part `X_1 = X - X_0` of an operator: the entries `X j i` with `|j| ≢ |i| (mod 2)`. -/
def oddPart (m n : ℕ) {N : ℕ} (X : Op m n N) : Op m n N :=
  fun j i => if tpar m j % 2 = tpar m i % 2 then 0 else X j i

/-- The action of `e_{a,b}` on `End` of the tensor space (p. 49):
`(x f)(u) = x(f(u)) - (-1)^{|x||f|} f(x u)` for homogeneous `f`, extended linearly to
`f = X_0 + X_1`; here `|x| = |a| + |b|`. As a matrix:
`E_{a,b} X - (X_0 E_{a,b} + (-1)^{|a|+|b|} X_1 E_{a,b})`. -/
def adE (m n : ℕ) {N : ℕ} (κ : Fin N → Bool) (a b : Fin (m + n)) : Op m n N →ₗ[ℂ] Op m n N where
  toFun X := actE m n κ a b * X -
    (evenPart m n X * actE m n κ a b + sgn (par m a + par m b) • (oddPart m n X * actE m n κ a b))
  map_add' X Y := by
    have h0 : evenPart m n (X + Y) = evenPart m n X + evenPart m n Y := by
      ext j i; simp only [evenPart, Matrix.add_apply]; split_ifs <;> simp
    have h1 : oddPart m n (X + Y) = oddPart m n X + oddPart m n Y := by
      ext j i; simp only [oddPart, Matrix.add_apply]; split_ifs <;> simp
    rw [h0, h1, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, smul_add]
    abel
  map_smul' z X := by
    have h0 : evenPart m n (z • X) = z • evenPart m n X := by
      ext j i; simp only [evenPart, Matrix.smul_apply]; split_ifs <;> simp
    have h1 : oddPart m n (z • X) = z • oddPart m n X := by
      ext j i; simp only [oddPart, Matrix.smul_apply]; split_ifs <;> simp
    simp only [RingHom.id_apply, h0, h1, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]
    rw [smul_comm z (sgn (par m a + par m b))]

/-- `End_g` of the tensor space (p. 49): all (not necessarily homogeneous) linear
endomorphisms annihilated by every `x ∈ g = gl_{m|n}(ℂ)`. Since the action on `End` is linear
in `x` and the matrix units `e_{a,b}` span `g`, these are the operators annihilated by every
`e_{a,b}`. -/
def EndG (m n : ℕ) {N : ℕ} (κ : Fin N → Bool) : Submodule ℂ (Op m n N) :=
  ⨅ a : Fin (m + n), ⨅ b : Fin (m + n), LinearMap.ker (adE m n κ a b)

/-- The slot pattern of `V^{⊗ N}`: every slot carries `V`. -/
def allV (N : ℕ) : Fin N → Bool := fun _ => true

/-- The slot pattern of `V^{⊗ r} ⊗ W^{⊗ s}`: the first `r` slots carry `V`, the last `s`
carry `W`. -/
def mixed (r s : ℕ) : Fin (r + s) → Bool := fun a => decide (a.val < r)

/-- The operator `Ω_{p,q}` of (7.3) for slots `p < q`:
`∑_{c,d} (-1)^{|d|} E^{(p)}_{c,d} E^{(q)}_{d,c}`. -/
def Omega (m n : ℕ) {N : ℕ} (κ : Fin N → Bool) (p q : Fin N) : Op m n N :=
  ∑ c : Fin (m + n), ∑ d : Fin (m + n),
    sgn (par m d) • (slotOp m n κ p c d * slotOp m n κ q d c)

/-- The parity `|i^R|` of the part of a multi-index at positions `≥ r`. -/
def rpar (m : ℕ) {n N : ℕ} (r : ℕ) (i : Fin N → Fin (m + n)) : ℕ :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin N => r ≤ a.val), par m (i a)

/-- `p(i^R) = ∑_{r ≤ a < b} |i_a||i_b|` (7.4), for the part of a multi-index at positions `≥ r`. -/
def rpp (m : ℕ) {n N : ℕ} (r : ℕ) (i : Fin N → Fin (m + n)) : ℕ :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin N => r ≤ a.val),
    ∑ b ∈ Finset.univ.filter (fun b : Fin N => a < b), par m (i a) * par m (i b)

/-- `u^L v^R`: the multi-index agreeing with `u` at positions `< r` and with `v` at
positions `≥ r`. -/
def splice {α : Type*} {N : ℕ} (r : ℕ) (u v : Fin N → α) : Fin N → α :=
  fun a => if a.val < r then u a else v a

/-- The map `flip_{r,s} : End(V^{⊗(r+s)}) → End(V^{⊗ r} ⊗ W^{⊗ s})` of (7.16), in coordinates:
`(flip X) a c = (-1)^{(|a^R| + |c^R|)|c^R| + p(a^R) + p(c^R)} X (a^L c^R) (c^L a^R)`.
That is, the matrix unit sending `v_{c^L} ⊗ v_{a^R}` to `v_{a^L} ⊗ v_{c^R}` goes to the
signed matrix unit sending `v_{c^L} ⊗ w_{c^R}` to `v_{a^L} ⊗ w_{a^R}` (identifications (7.13),
(7.15), (7.18)). -/
def flipEnd (m n r s : ℕ) : Op m n (r + s) →ₗ[ℂ] Op m n (r + s) where
  toFun X := Matrix.of fun a c =>
    sgn ((rpar m r a + rpar m r c) * rpar m r c + rpp m r a + rpp m r c) *
      X (splice r a c) (splice r c a)
  map_add' X Y := by ext a c; simp only [Matrix.of_apply, Matrix.add_apply]; ring
  map_smul' z X := by
    ext a c; simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

end WalledBrauer.SuperSchurWeyl


