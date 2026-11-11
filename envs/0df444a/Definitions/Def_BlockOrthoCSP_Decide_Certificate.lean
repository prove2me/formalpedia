-- Prove2me | Definitions.Def_BlockOrthoCSP_Decide_Certificate
-- name    : BlockOrthoCSP_Decide_Certificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:14:07.148433+00:00
-- url     : https://prove2.me/theorems/e8784e3e-1112-4609-bf08-cc9c6196ec26
-- title:
--   Block Orthogonality certificates (Definition F.4.1), $V_K(E)$, $B_k$ and $Q_k$
-- statement:
--   Fix an arity $k = j+1 \ge 2$, rows $\mathcal R_k = D^{j}$ (ordered lexicographically) and columns $D$, and variables $X_{x,c}$ for the entries. A **Block Orthogonality certificate** (Definition F.4.1) chooses: a rectangle system $(R_1,C_1),\dots,(R_t,C_t)$ with nonempty, pairwise disjoint row sets and nonempty, pairwise disjoint column sets ($t=0$ allowed), imposing $X_{x,c} = 0$ outside $\bigcup_i R_i\times C_i$ (F.18); for distinct rows $x,y$ of one $R_i$ and distinct columns $c,e$ of $C_i$ a root $\tau \in \mu(K)$ and the twisted minor $X_{x,c}X_{y,e} - \tau X_{x,e}X_{y,c}$ (F.19); for each pair $x<y$ in one $R_i$ either **dependent mode**, all minors $X_{x,c}X_{y,e} - X_{x,e}X_{y,c}$ (F.20), or **orthogonal mode**: a partition of $C_i$ into blocks $T$ with anchors $c_T$, roots $\rho_{T,c}, \sigma_{T,c} \in \mu(K)$ with $\rho_{T,c_T} = \sigma_{T,c_T} = 1$, retained only if
--   $$\sum_{c\in T} \rho_{T,c}\,\overline{\sigma_{T,c}} = 0 \quad (F.21),$$
--   and anchor equations $X_{x,c} - \rho_{T,c}X_{x,c_T}$, $X_{y,c} - \sigma_{T,c}X_{y,c_T}$ (F.22)–(F.23). $E_c$ is the set of these left-hand sides and $C_k$ the set of retained certificates.
--
--   $V_K(E)$ is the set of $K$-valued $A$ on $D^k$ annihilated by every $e \in E$; $B_k$ is the set of $K$-valued $k$-ary functions all of whose singleton purifications are block-orthogonal. With $E_c' = E_c \setminus \{0\}$: $Q_k = \emptyset$ if some $E_c'$ is empty, and otherwise $Q_k = \{\prod_{c \in C_k} e_c : e_c \in E_c'\}$.
--
--   **Formalization Note.** A block partition with anchors is encoded by the anchor map $c \mapsto c_T$ (blocks = fibres, anchors = fixed points), and entries the definition does not use are pinned to defaults, so certificates are exactly the paper's choices. Twisted minors are imposed for ordered pairs of distinct rows and columns.
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), pp. F-15–F-18, Definition F.4.1, Eqs. (F.18)–(F.23), definitions of V_K(E), B_k (p. F-16) and Q_k (p. F-18)

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Rows
import Definitions.Def_BlockOrthoCSP_Decide_Purification
import Definitions.Def_BlockOrthoCSP_Decide_NumberField

set_option autoImplicit false

namespace BlockOrthoCSP.Decide

open ComplexConjugate

/-- The data of a Block Orthogonality certificate of arity `k = j + 1` (Definition F.4.1,
p. F-15), rows `R_k = D^j`, columns `D`:
* a rectangle system `(R_1, C_1), …, (R_t, C_t)` (`t = 0` allowed);
* `τ x y c e`, the root in the twisted minor (F.19) for distinct rows `x, y` of one `R_i` and
  distinct columns `c, e` of `C_i`;
* for each pair `x < y` (lexicographic order) in one `R_i`, the mode: `orth x y = false` is
  dependent mode, `true` orthogonal mode;
* in orthogonal mode, the set partition `T_{x,y}` of `C_i` with its anchors, encoded by the
  anchor map `anc x y : C_i → C_i` (`c ↦ c_T` for `c ∈ T`; the blocks are its fibres and the
  anchors its fixed points), and the roots `ρ x y c = ρ_{T,c}`, `σ x y c = σ_{T,c}`.
Entries not used by the definition are fixed to a default (`1`, `false`, `c`) by `IsCert`,
so certificates correspond exactly to the paper's discrete choices. -/
structure CertData (q j : ℕ) where
  t : ℕ
  R : Fin t → Finset (Fin j → Fin q)
  C : Fin t → Finset (Fin q)
  τ : (Fin j → Fin q) → (Fin j → Fin q) → Fin q → Fin q → ℂ
  orth : (Fin j → Fin q) → (Fin j → Fin q) → Bool
  anc : (Fin j → Fin q) → (Fin j → Fin q) → Fin q → Fin q
  ρ : (Fin j → Fin q) → (Fin j → Fin q) → Fin q → ℂ
  σ : (Fin j → Fin q) → (Fin j → Fin q) → Fin q → ℂ

namespace CertData

variable {q j : ℕ} (d : CertData q j)

/-- `(x, c) ∈ ⋃_i R_i × C_i`. -/
def InRect (x : Fin j → Fin q) (c : Fin q) : Prop :=
  ∃ i, x ∈ d.R i ∧ c ∈ d.C i

/-- `x, y` distinct rows of one `R_i` and `c, e` distinct columns of `C_i` (F.19). -/
def TwistRel (x y : Fin j → Fin q) (c e : Fin q) : Prop :=
  ∃ i, x ∈ d.R i ∧ y ∈ d.R i ∧ x ≠ y ∧ c ∈ d.C i ∧ e ∈ d.C i ∧ c ≠ e

/-- `x < y` (lexicographic order on `D^j`, the "fixed arbitrary total order") in one `R_i`. -/
def PairRel (x y : Fin j → Fin q) : Prop :=
  (∃ i, x ∈ d.R i ∧ y ∈ d.R i) ∧ toLex x < toLex y

/-- The column set `C_i` of the rectangle whose row set contains `x` (empty if none). -/
def cols (x : Fin j → Fin q) : Set (Fin q) :=
  {c | ∃ i, x ∈ d.R i ∧ c ∈ d.C i}

/-- `x < y` in one `R_i`, in orthogonal mode, and `c ∈ C_i`. -/
def OrthRel (x y : Fin j → Fin q) (c : Fin q) : Prop :=
  d.PairRel x y ∧ d.orth x y = true ∧ c ∈ d.cols x

open scoped Classical in
/-- The conditions of Definition F.4.1 for the root set `mu = µ(K)`, including retention
(F.21): `∑_{c ∈ T} ρ_{T,c} conj(σ_{T,c}) = 0` for every block `T`. -/
def IsCert (mu : Set ℂ) : Prop :=
  (∀ i, (d.R i).Nonempty ∧ (d.C i).Nonempty) ∧
  (∀ i i', i ≠ i' → Disjoint (d.R i) (d.R i') ∧ Disjoint (d.C i) (d.C i')) ∧
  (∀ x y c e, (d.TwistRel x y c e → d.τ x y c e ∈ mu) ∧
    (¬ d.TwistRel x y c e → d.τ x y c e = 1)) ∧
  (∀ x y, ¬ d.PairRel x y → d.orth x y = false) ∧
  (∀ x y c, d.OrthRel x y c →
    d.anc x y c ∈ d.cols x ∧ d.anc x y (d.anc x y c) = d.anc x y c ∧
    d.ρ x y c ∈ mu ∧ d.σ x y c ∈ mu ∧
    (d.anc x y c = c → d.ρ x y c = 1 ∧ d.σ x y c = 1)) ∧
  (∀ x y c, ¬ d.OrthRel x y c → d.anc x y c = c ∧ d.ρ x y c = 1 ∧ d.σ x y c = 1) ∧
  (∀ x y c₀, d.OrthRel x y c₀ → d.anc x y c₀ = c₀ →
    ∑ c ∈ Finset.univ.filter (fun c => d.OrthRel x y c ∧ d.anc x y c = c₀),
      d.ρ x y c * conj (d.σ x y c) = 0)

/-- The formal variable `X_{x,c}` (the entry `F(x, c)`), indexed by `(x, c) ∈ D^{j+1}`. -/
noncomputable def Xv (x : Fin j → Fin q) (c : Fin q) : MvPolynomial (Fin (j + 1) → Fin q) ℂ :=
  MvPolynomial.X (Fin.snoc x c)

/-- `E_c`, the left-hand sides of the certificate's equations: support equations (F.18),
twisted minors (F.19), ordinary minors in dependent mode (F.20), anchor equations
(F.22)–(F.23) in orthogonal mode (`c ∈ T \ {c_T}`). -/
def eqs : Set (MvPolynomial (Fin (j + 1) → Fin q) ℂ) :=
  {P | ∃ x c, ¬ d.InRect x c ∧ P = Xv x c} ∪
  {P | ∃ x y c e, d.TwistRel x y c e ∧
    P = Xv x c * Xv y e - MvPolynomial.C (d.τ x y c e) * Xv x e * Xv y c} ∪
  {P | ∃ x y c e, d.PairRel x y ∧ d.orth x y = false ∧ c ∈ d.cols x ∧ e ∈ d.cols x ∧
    P = Xv x c * Xv y e - Xv x e * Xv y c} ∪
  {P | ∃ x y c, d.OrthRel x y c ∧ d.anc x y c ≠ c ∧
    (P = Xv x c - MvPolynomial.C (d.ρ x y c) * Xv x (d.anc x y c) ∨
     P = Xv y c - MvPolynomial.C (d.σ x y c) * Xv y (d.anc x y c))}

end CertData

/-- `C_k` for `k = j + 1`: the retained certificates over `µ(K)`, `K` the field (F.13) of `F`. -/
def certs {q : ℕ} (F : Finset (CFn q)) (j : ℕ) : Set (CertData q j) :=
  {d | d.IsCert (muK F)}

/-- `V_K(E) = {A ∈ K^{D^k} : e(A) = 0 for every e ∈ E}` (p. F-16). -/
def VK {q : ℕ} (F : Finset (CFn q)) {j : ℕ} (E : Set (MvPolynomial (Fin (j + 1) → Fin q) ℂ)) :
    Set ((Fin (j + 1) → Fin q) → ℂ) :=
  {A | (∀ a, A a ∈ fieldK F) ∧ ∀ P ∈ E, MvPolynomial.eval A P = 0}

/-- `B_k` for `k = j + 1` (p. F-16): the `K`-valued `k`-ary functions whose singleton
purifications are block-orthogonal. -/
def Bk {q : ℕ} (F : Finset (CFn q)) (j : ℕ) : Set ((Fin (j + 1) → Fin q) → ℂ) :=
  {A | (∀ a, A a ∈ fieldK F) ∧
    ∀ A' : (Fin (j + 1) → Fin q) → ℂ, IsSingletonPurification A A' → IsBlockOrthogonal A'}

open scoped Classical in
/-- `Q_k` for `k = j + 1` (p. F-18): with `E_j` the certificates' equation sets after deleting
the (syntactically) zero polynomials, `Q_k = ∅` if some `E_j` is empty and otherwise the set of
products `∏_j e_j` with one `e_j ∈ E_j` from every retained certificate. (`C_k` is finite;
`finprod` is the product over it.) -/
noncomputable def Qk {q : ℕ} (F : Finset (CFn q)) (j : ℕ) :
    Set (MvPolynomial (Fin (j + 1) → Fin q) ℂ) :=
  if ∃ d ∈ certs F j, d.eqs \ {0} = ∅ then ∅ else
    {P | ∃ e : certs F j → MvPolynomial (Fin (j + 1) → Fin q) ℂ,
      (∀ d, e d ∈ d.1.eqs \ {0}) ∧ P = ∏ᶠ d, e d}

end BlockOrthoCSP.Decide


