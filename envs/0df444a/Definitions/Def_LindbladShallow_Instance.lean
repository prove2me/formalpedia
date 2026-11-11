-- Prove2me | Definitions.Def_LindbladShallow_Instance
-- name    : LindbladShallow_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:17:18.255196+00:00
-- url     : https://prove2.me/theorems/2ce3e658-eba8-4e5e-a22e-cc6cffc98751
-- title:
--   Fixed local parameters, input instances, validity, retained terms and lifting
-- statement:
--   The **fixed local parameters** are the lattice dimension $D\ge1$, the number $d_0\ge1$ of qubits per site, the support-size bound $\kappa\ge1$, the $\ell^\infty$ support-diameter bound $r_*\ge1$, the jump-multiplicity bound $\mu_*\ge1$ and the incidence bound $d_{\mathrm{inc}}\ge1$.
--
--   An **input** consists of a list of sites $\Lambda\subset\mathbb Z^D$ ($n$ sites), an ordered list of terms, a rational time $T$ and a rational tolerance $\epsilon$. Each term has an ordered support $X_e$ (a list of sites fixing the tensor-factor order) and either one local Hamiltonian matrix $H_e$ ($e\in I_H$) or a list of jump matrices $L_{e1},\dots,L_{e\mu_e}$ ($e\in I_J$), all with entries in $\mathbb Q+i\mathbb Q$ and indexed by the qubits of the support. A term is **retained** if its support is nonempty and it is not exactly zero.
--
--   The input is **valid** if:
--   1. the sites are distinct and $n\ge1$;
--   2. $T>0$ and $0<\epsilon<1$;
--   3. every support has distinct sites, all in $\Lambda$;
--   4. every $H_e$ is Hermitian;
--   5. every dissipative term has $1\le\mu_e\le\mu_*$;
--   6. every retained term has $|X_e|\le\kappa$ and $\mathrm{diam}_\infty X_e\le r_*$;
--   7. every site meets at most $d_{\mathrm{inc}}$ retained terms.
--
--   A local matrix is **lifted** to the $n d_0$-qubit system by acting as itself on the qubits of its support (in support order) and as the identity elsewhere.
--
--   This is the local input model of §2.1 under which Theorem 2.1 is stated.
--
--   **Formalization Note** Matrix dimensions are enforced by typing. Non-retained terms are allowed in the input and are exempt from 6–7, as in the paper, where preprocessing removes them.
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), §2.1, p.9; Theorem 2.1, p.10

import Mathlib
import Definitions.Def_LindbladShallow_gksl

open scoped Matrix ComplexOrder

namespace LindbladShallow

/-- The fixed local parameters of the model (arXiv:2610.05362, held version sha256 8f4637ef…,
§2.1, p.9): the lattice dimension `D ≥ 1`, the number `d0` of system qubits per site, the bound
`κ ≥ 1` on the support size, the bound `r∗ ≥ 1` on the ℓ∞ support diameter, the bound `µ∗ ≥ 1` on
the jump multiplicity, and the incidence bound `d_inc ≥ 1`.

**Formalization Note** `d0 ≥ 1` is implicit in "d0 system qubits per site" and is recorded as a
field. -/
structure Params where
  D : ℕ
  d0 : ℕ
  κ : ℕ
  rstar : ℕ
  μstar : ℕ
  dinc : ℕ
  hD : 1 ≤ D
  hd0 : 1 ≤ d0
  hκ : 1 ≤ κ
  hrstar : 1 ≤ rstar
  hμstar : 1 ≤ μstar
  hdinc : 1 ≤ dinc

/-- A lattice site, a point of `ℤ^D`. -/
abbrev Site (P : Params) := Fin P.D → ℤ

/-- Computational basis of the qubits of an ordered support of `m` sites with `d0` qubits per site:
`(i, k)` is qubit `k` of the `i`-th support site. -/
abbrev LocBasis (d0 m : ℕ) := Fin m × Fin d0 → Bool

/-- A local matrix with entries in `ℚ + iℚ`, entry `(a, b)` meaning `a + i b`. -/
abbrev QIMat (d0 m : ℕ) := Matrix (LocBasis d0 m) (LocBasis d0 m) (ℚ × ℚ)

/-- The complex number `a + i b`. -/
noncomputable def toC (q : ℚ × ℚ) : ℂ := (q.1 : ℂ) + (q.2 : ℂ) * Complex.I

/-- A `ℚ + iℚ` matrix read as a complex matrix. -/
noncomputable def cmat {d0 m : ℕ} (A : QIMat d0 m) : Matrix (LocBasis d0 m) (LocBasis d0 m) ℂ :=
  A.map toC

/-- The local data of one term on its ordered support of `m` sites: a Hamiltonian term carries one
local matrix `H_e` (`e ∈ I_H`), a dissipative term carries its list of jump components
`L_{e1}, …, L_{eµ_e}` (`e ∈ I_J`) (arXiv:2610.05362, §2.1, p.9). The tag makes `I_H`, `I_J`
disjoint. -/
inductive TermData (d0 m : ℕ)
  | ham (H : QIMat d0 m)
  | jump (L : List (QIMat d0 m))

/-- One term of the input: its ordered support list `X_e` (sites of `ℤ^D`, fixing the
tensor-factor order of its local matrices) and its local data. -/
structure Term (P : Params) where
  supp : List (Site P)
  data : TermData P.d0 supp.length

/-- A raw input (arXiv:2610.05362, §2.1, p.9): the site list `Λ ⊂ ℤ^D` (`n` = its length), the
ordered term list, the rational evolution time `T` and the rational tolerance `ϵ`. -/
structure Instance (P : Params) where
  sites : List (Site P)
  terms : List (Term P)
  T : ℚ
  ε : ℚ

/-- The number `n` of sites. -/
abbrev Instance.n {P : Params} (I : Instance P) : ℕ := I.sites.length

/-- The number of terms. -/
abbrev Instance.nT {P : Params} (I : Instance P) : ℕ := I.terms.length

/-- The `e`-th term. -/
abbrev Instance.term {P : Params} (I : Instance P) (e : Fin I.nT) : Term P := I.terms.get e

/-- System computational basis: an assignment of a bit to qubit `k` of site `j`
(`j : Fin n` indexes `Λ` in list order; within each site qubits are ordered by index). -/
abbrev Sys {P : Params} (I : Instance P) := Fin I.n × Fin P.d0 → Bool

/-- An exact-zero term: a zero Hamiltonian matrix, or all jump components zero. -/
def Term.IsZero {P : Params} (t : Term P) : Prop :=
  match t.data with
  | .ham H => H = 0
  | .jump L => ∀ A ∈ L, A = 0

/-- A retained term (arXiv:2610.05362, §2.1, p.9): preprocessing removes empty-support terms and
exact-zero terms; the retained ones have nonempty support and are not exactly zero. -/
def Term.Retained {P : Params} (t : Term P) : Prop :=
  t.supp ≠ [] ∧ ¬ t.IsZero

/-- A jump (dissipative) term, `e ∈ I_J`. -/
def Term.IsJump {P : Params} (t : Term P) : Prop :=
  match t.data with
  | .ham _ => False
  | .jump _ => True

/-- The complex Hamiltonian matrix of a term (`0` for a dissipative term). -/
noncomputable def Term.hamC {P : Params} (t : Term P) :
    Matrix (LocBasis P.d0 t.supp.length) (LocBasis P.d0 t.supp.length) ℂ :=
  match t.data with
  | .ham H => cmat H
  | .jump _ => 0

/-- The complex jump components of a term (empty for a Hamiltonian term). -/
noncomputable def Term.jumpsC {P : Params} (t : Term P) :
    List (Matrix (LocBasis P.d0 t.supp.length) (LocBasis P.d0 t.supp.length) ℂ) :=
  match t.data with
  | .ham _ => []
  | .jump L => L.map cmat

/-- Validity of an input under the local assumptions (arXiv:2610.05362, §2.1, p.9, and
Theorem 2.1, p.10):
1. `Λ` is a list of distinct sites with `n ≥ 1`;
2. `T > 0` and `0 < ϵ < 1` (Theorem 2.1);
3. every support list has distinct entries, all in `Λ`;
4. every Hamiltonian matrix is Hermitian, `H_e = H_e†`;
5. every dissipative term has `1 ≤ µ_e ≤ µ∗` jump components;
6. every retained term has `|X_e| ≤ κ` and `diam_∞ X_e ≤ r∗`;
7. every site meets at most `d_inc` retained terms.

**Formalization Note** Matrix dimensions are checked by typing (a local matrix is indexed by the
qubits of its support). Non-retained terms (empty support, or exactly zero) are allowed and are
not subject to 6–7, as in the paper, where preprocessing removes them; they contribute `0` to the
generator. -/
structure Instance.Valid {P : Params} (I : Instance P) : Prop where
  sites_nodup : I.sites.Nodup
  sites_ne : I.sites ≠ []
  T_pos : 0 < I.T
  ε_pos : 0 < I.ε
  ε_lt_one : I.ε < 1
  supp_nodup : ∀ e : Fin I.nT, (I.term e).supp.Nodup
  supp_sub : ∀ e : Fin I.nT, ∀ x ∈ (I.term e).supp, x ∈ I.sites
  herm : ∀ e : Fin I.nT, ∀ H, (I.term e).data = .ham H → (cmat H).IsHermitian
  jump_count : ∀ e : Fin I.nT, ∀ L, (I.term e).data = .jump L →
    1 ≤ L.length ∧ L.length ≤ P.μstar
  supp_card : ∀ e : Fin I.nT, (I.term e).Retained → (I.term e).supp.length ≤ P.κ
  supp_diam : ∀ e : Fin I.nT, (I.term e).Retained →
    ∀ x ∈ (I.term e).supp, ∀ y ∈ (I.term e).supp, ∀ j, |x j - y j| ≤ (P.rstar : ℤ)
  incidence : ∀ x ∈ I.sites, ∀ s : Finset (Fin I.nT),
    (∀ e ∈ s, (I.term e).Retained ∧ x ∈ (I.term e).supp) → s.card ≤ P.dinc

/-- The local configuration seen by an ordered support `X`: bit `(i, k)` is the bit of qubit `k` at
the site of `Λ` equal to `X[i]`. -/
def locCfg {P : Params} (I : Instance P) (X : List (Site P)) (σ : Sys I) :
    LocBasis P.d0 X.length :=
  fun p => decide (∃ j : Fin I.n, I.sites.get j = X.get p.1 ∧ σ (j, p.2) = true)

/-- Two system configurations agree off the support `X`. -/
def AgreeOff {P : Params} (I : Instance P) (X : List (Site P)) (σ' σ : Sys I) : Prop :=
  ∀ j : Fin I.n, ∀ k : Fin P.d0, I.sites.get j ∉ X → σ' (j, k) = σ (j, k)

/-- Lift of a local matrix on the qubits of the ordered support `X` to the whole system, by the
identity off the support: `(lift A)_{σ'σ} = A_{σ'|_X, σ|_X}` when `σ'`, `σ` agree off `X`, else `0`
(arXiv:2610.05362, Eq. (1): `H_e`, `L_eµ` act on `X_e`; §2.1: the ordered support fixes the
tensor-factor order). -/
noncomputable def liftSys {P : Params} (I : Instance P) (X : List (Site P))
    (A : Matrix (LocBasis P.d0 X.length) (LocBasis P.d0 X.length) ℂ) :
    Matrix (Sys I) (Sys I) ℂ :=
  open Classical in
  Matrix.of fun σ' σ => if AgreeOff I X σ' σ then A (locCfg I X σ') (locCfg I X σ) else 0

/-- Lift of a local matrix on (support qubits) ⊗ `A` to (system) ⊗ `A`, by the identity on the
system qubits off the support (used for a jump Cayley gate with its own bath register). -/
noncomputable def liftSysX {P : Params} (I : Instance P) (X : List (Site P)) {α : Type*}
    (A : Matrix (LocBasis P.d0 X.length × α) (LocBasis P.d0 X.length × α) ℂ) :
    Matrix (Sys I × α) (Sys I × α) ℂ :=
  open Classical in
  Matrix.of fun p q =>
    if AgreeOff I X p.1 q.1 then A (locCfg I X p.1, p.2) (locCfg I X q.1, q.2) else 0

end LindbladShallow


