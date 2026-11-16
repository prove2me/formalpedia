-- Prove2me | Definitions.Def_PrivPCP_Supplement_ZOSInstance
-- name    : PrivPCP_Supplement_ZOSInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:56:24.703177+00:00
-- url     : https://prove2.me/theorems/18abffe6-c506-4ec2-bb5d-c2bdd3d56c29
-- title:
--   The $k$-dimensional zero-on-subcube problem and its function $f_I$ (Definition 5.1)
-- statement:
--   Fix $k\ge2$ and a prime $q$. For $i\in[k]$ let $\Gamma_i=\langle\omega_i\rangle\le\mathbb F_q^\times$ have order $h_i$, choose $\zeta_i\in\mathbb F_q^\times$, and put $H_i=\zeta_i\Gamma_i$, $D=\prod_{i=1}^kH_i$. For $a\in\{0,\dots,h_i-1\}$ the one-coordinate shift is $\sigma_{i,a}(x_1,\dots,x_k)=(x_1,\dots,\omega_i^ax_i,\dots,x_k)$. A **$k$-dimensional zero-on-subcube instance** $I=(\mathbb F_q,D,\Psi,C)$ consists of a labeled list $\Psi=(\psi_1,\dots,\psi_t)$ of identities and one-coordinate shifts, and a polynomial $C(X,Y_1,\dots,Y_t)\in\mathbb F_q[X_1,\dots,X_k,Y_1,\dots,Y_t]$ with $\deg_{X_i}C<h_i$ for every $i$ and $\deg_YC\le3$.
--
--   For a table $A:D\to\mathbb F_q$ with interpolant $\tilde A$ ($\deg_{X_i}\tilde A<h_i$), put $B_A(X)=C(X,\tilde A(\psi_1(X)),\dots,\tilde A(\psi_t(X)))$. The **zero-on-subcube function** is
--   $$
--   f_I(A)=\begin{cases}1,&B_A|_D\equiv0,\\0,&\text{otherwise.}\end{cases}
--   $$
--   The description of $I$, whose length is $\mathrm{size}(I)$, lists $q$, $k$, the $\omega_i$, $\zeta_i$, $h_i$, the list $\Psi$ and the monomials of $C$, all numbers in binary.
--
--   **Formalization Note** $C$ is given by a list of monomials, each with $X_i$-degree $<h_i$ and total $Y$-degree $\le3$; every polynomial with these degree bounds is the sum of such a list. Every map in $\Psi$ preserves $D$, so for $z\in D$ the values $\tilde A(\psi_j(z))$ are $A(\psi_j(z))$, which is how $f_I$ is computed. $\deg_YC$ is the total degree in $Y_1,\dots,Y_t$.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Definition 5.1, pp.26–27 (PDF pp.28–29)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_ZKSheafPCP_queryLog

set_option autoImplicit false

open QAlgorithms.Complexity QAdvFew.PoQOracle ZKSheafPCP

namespace PrivPCP.Supplement

/-- A **`k`-dimensional zero-on-subcube instance** `I = (𝔽_q, D, Ψ, C)` (Bafna, Vyas, *Private PCPs
from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Definition 5.1,
pp.26–27): generators `ω_i` of the subgroups `Γ_i = ⟨ω_i⟩ ⩽ 𝔽_q^×` of orders `h_i`, shifts
`ζ_i ∈ 𝔽_q^×` (so `H_i = ζ_i Γ_i` and `D = ∏_i H_i`), the labeled list `Ψ = (ψ_1, …, ψ_t)` (`none` is
the identity, `some (i, a)` the one-coordinate shift `σ_{i,a}(x) = (…, ω_i^a x_i, …)`), and the
constraint polynomial `C(X, Y) ∈ 𝔽_q[X_1, …, X_k, Y_1, …, Y_t]` as its list of monomials
`(c, e, f)` standing for `c · ∏_i X_i^{e_i} · ∏_j Y_j^{f_j}`.

**Formalization Note** The polynomial `C` is given by a list of monomials; every polynomial with
`deg_{X_i} C < h_i` and `deg_Y C ⩽ 3` is the sum of such a list whose monomials satisfy these
bounds (`IsValid`). The list is what `code` writes down. -/
structure ZOSInstance (q k : ℕ) where
  /-- generators `ω_i` -/
  ω : Fin k → (ZMod q)ˣ
  /-- coset shifts `ζ_i` -/
  ζ : Fin k → (ZMod q)ˣ
  /-- orders `h_i` -/
  h : Fin k → ℕ
  /-- the labeled list `Ψ` -/
  Ψ : List (Option (Fin k × ℕ))
  /-- the monomials of `C` -/
  Cmon : List (ZMod q × (Fin k → ℕ) × (Fin Ψ.length → ℕ))

namespace ZOSInstance

variable {q k : ℕ} (I : ZOSInstance q k)

/-- The conditions of Definition 5.1: `k ⩾ 2`, `ω_i` has order `h_i`, every shift `σ_{i,a}` has
`a ∈ {0, …, h_i − 1}`, and every monomial of `C` has `X_i`-degree `< h_i` and total `Y`-degree `⩽ 3`. -/
def IsValid : Prop :=
  2 ≤ k ∧ (∀ i, orderOf (I.ω i) = I.h i) ∧
  (∀ ψ ∈ I.Ψ, ∀ i a, ψ = some (i, a) → a < I.h i) ∧
  (∀ m ∈ I.Cmon, (∀ i, m.2.1 i < I.h i) ∧ ∑ j, m.2.2 j ≤ 3)

/-- `H_i = ζ_i Γ_i ⊆ 𝔽_q`. -/
noncomputable def H [NeZero q] (i : Fin k) : Finset (ZMod q) :=
  open Classical in
  Finset.univ.filter fun z => ∃ γ ∈ Subgroup.zpowers (I.ω i), ((I.ζ i * γ : (ZMod q)ˣ) : ZMod q) = z

/-- The constraint grid `D = ∏_i H_i ⊆ 𝔽_q^k`. -/
noncomputable def Dset [NeZero q] : Finset (Fin k → ZMod q) :=
  open Classical in
  Finset.univ.filter fun z => ∀ i, z i ∈ I.H i

/-- The map `ψ` on `𝔽_q^k`: the identity, or `σ_{i,a}`. -/
def shift (ψ : Option (Fin k × ℕ)) (z : Fin k → ZMod q) : Fin k → ZMod q :=
  match ψ with
  | none => z
  | some (i, a) => Function.update z i (((I.ω i ^ a : (ZMod q)ˣ) : ZMod q) * z i)

/-- `C(x, y)`. -/
def Ceval (x : Fin k → ZMod q) (y : Fin I.Ψ.length → ZMod q) : ZMod q :=
  (I.Cmon.map fun m => m.1 * (∏ i, x i ^ m.2.1 i) * ∏ j, y j ^ m.2.2 j).sum

/-- A table `A : D → 𝔽_q`, extended by `0` outside `D`. -/
noncomputable def ext [NeZero q] (A : ↥I.Dset → ZMod q) (z : Fin k → ZMod q) : ZMod q :=
  open Classical in
  if h : z ∈ I.Dset then A ⟨z, h⟩ else 0

/-- The **zero-on-subcube function** `f_I(A)` (Definition 5.1, p.27): `1` if `A` satisfies `I`, that
is `B_A|_D ≡ 0` with `B_A(z) = C(z, Ã(ψ_1(z)), …, Ã(ψ_t(z)))`, and `0` otherwise.

**Formalization Note** The paper evaluates the interpolant `Ã` of `A` (`deg_{X_i} Ã < h_i`) at the
points `ψ_j(z)`. Every map in `Ψ` preserves `D` (`ω_i^a ∈ Γ_i`), so for `z ∈ D` these values are
`A(ψ_j(z))`, which is how they are computed here. -/
noncomputable def fI [NeZero q] (A : ↥I.Dset → ZMod q) : ZMod q :=
  open Classical in
  if ∀ z : ↥I.Dset, I.Ceval z.1 (fun j => I.ext A (I.shift (I.Ψ.get j) z.1)) = 0 then 1 else 0

/-- The **description** of `I`, whose length is `size(I)`: `q`, `k`, the `ω_i`, `ζ_i`, `h_i`, the
list `Ψ`, and the monomials of `C`, all numbers in binary. -/
def code : Str :=
  tup [binN q, binN k,
    tup (List.ofFn fun i => binN ((I.ω i : ZMod q)).val),
    tup (List.ofFn fun i => binN ((I.ζ i : ZMod q)).val),
    tup (List.ofFn fun i => binN (I.h i)),
    tup (I.Ψ.map fun ψ => match ψ with
      | none => tup []
      | some (i, a) => tup [binN i.val, binN a]),
    tup (I.Cmon.map fun m => tup [binN m.1.val, tup (List.ofFn fun i => binN (m.2.1 i)),
      tup (List.ofFn fun j => binN (m.2.2 j))])]

end ZOSInstance

end PrivPCP.Supplement


