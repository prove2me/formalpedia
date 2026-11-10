-- Prove2me | Definitions.Def_UniformSubpower_Supplied_SparseCentral
-- name    : UniformSubpower_Supplied_SparseCentral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:19:59.731712+00:00
-- url     : https://prove2.me/theorems/db85ac2b-eaf9-47e0-9f42-2bffbe9bcce4
-- title:
--   The sparse central setting of §8: physical rows, affine sparse operations, a rowwise Mal'tsev operation and T = Sg(H)
-- statement:
--   There are $M$ **physical rows** $v$, each with a chart alphabet $A_v = L_v \times Q_v$, where $L_v$ is a finite abelian group and $Q_v$ a finite set; a tuple is $x = (x_v)_v \in \prod_v A_v$, with quotient projection $\pi(x) = (q_v)_v$ for $x_v = (\ell_v, q_v)$, and central translation $(x + d)_v = (\ell_v + d_v, q_v)$ for $d \in \prod_v L_v$.
--
--   A **checked sparse operation** $f$ of global arity $r$ has, for each output row $v$, a reference list $R_{f,v} \subseteq \{1, \dots, r\} \times \{1, \dots, M\}$ whose projection to the first component is injective, and the affine form (16):
--   $$f_v(x) = \Big( \sum_{(j,u) \in R_{f,v}} \varphi_{f,v,j,u}(\ell^j_u) + c_{f,v}\big((q^j_u)_{(j,u) \in R_{f,v}}\big),\ f_{Q,v}\big((q^j_u)_{(j,u) \in R_{f,v}}\big) \Big),$$
--   with additive homomorphisms $\varphi_{f,v,j,u} : L_u \to L_v$ that do not depend on the quotient entries. The signature also contains a **rowwise Mal'tsev operation** $m$ with coefficients $(\mathrm{id}, -\mathrm{id}, \mathrm{id})$: $m_v((\ell_1, q_1), (\ell_2, q_2), (\ell_3, q_3)) = (\ell_1 - \ell_2 + \ell_3 + c_v(q_1, q_2, q_3),\ \bar m_v(q_1, q_2, q_3))$, satisfying $m(x, y, y) = x$ and $m(x, x, y) = y$ on every row. Given a nonempty set $H$ of tuples, $T = \mathrm{Sg}(H)$ is the least set of tuples containing $H$ and closed under all sparse operations and $m$.
--
--   **Formalization Note.** An operation is given by its affine data rather than by small tables that are checked to have the affine form; the two describe the same operations.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), p. 22, §8, (16), (17)

import Mathlib

namespace UniformSubpower.Supplied

/-!
The sparse central setting of §8 (Gkantzounis, p. 22): `M` physical rows with chart alphabets
`A_v = L_v × Q_v`, `L_v` a finite abelian group; checked sparse operations of the affine
form (16); an explicit rowwise Mal'tsev operation `m` with coefficients `(id, −id, id)`, (17);
a nonempty input list `H` and `T = Sg(H)`.
-/

/-- A whole tuple over the physical rows: an entry `(ℓ_v, q_v) ∈ L_v × Q_v` at every row `v`. -/
abbrev RowTuple (M : ℕ) (L Q : Fin M → Type) : Type := (v : Fin M) → L v × Q v

/-- A checked sparse operation of global arity `arity`, in the affine chart form (16):
at output row `v` it reads only the entries listed in its reference list
`R_{f,v} ⊆ {global arguments} × {rows}`, whose projection to the first component is injective,
and outputs
`(∑_{(j,u) ∈ R_{f,v}} φ_{f,v,j,u}(ℓ^j_u) + c_{f,v}((q^j_u)), f_{Q,v}((q^j_u)))`
with additive homomorphisms `φ_{f,v,j,u} : L_u → L_v` independent of the quotient entries. -/
structure SparseOp (M : ℕ) (L Q : Fin M → Type) [∀ v, AddCommGroup (L v)] where
  arity : ℕ
  refs : Fin M → Finset (Fin arity × Fin M)
  refs_inj : ∀ v, ∀ p ∈ refs v, ∀ p' ∈ refs v, p.1 = p'.1 → p = p'
  coef : (v : Fin M) → (p : Fin arity × Fin M) → (L p.2 →+ L v)
  const : (v : Fin M) → ((p : refs v) → Q p.1.2) → L v
  quot : (v : Fin M) → ((p : refs v) → Q p.1.2) → Q v

/-- Evaluation of a sparse operation on `arity` whole tuples. -/
def SparseOp.eval {M : ℕ} {L Q : Fin M → Type} [∀ v, AddCommGroup (L v)]
    (f : SparseOp M L Q) (x : Fin f.arity → RowTuple M L Q) : RowTuple M L Q :=
  fun v =>
    (∑ p ∈ (f.refs v).attach, f.coef v p.1 (x p.1.1 p.1.2).1 +
        f.const v (fun p => (x p.1.1 p.1.2).2),
      f.quot v (fun p => (x p.1.1 p.1.2).2))

/-- The data of §8: the sparse signature `ops`, the rowwise Mal'tsev operation `m` given by
its quotient tables `mQ` and constants `mc` (coefficients `(id, −id, id)`), with the Mal'tsev
identities checked on every row, and a nonempty input list `H`. -/
structure CentralSetting (M : ℕ) (L Q : Fin M → Type) [∀ v, AddCommGroup (L v)]
    [∀ v, Fintype (L v)] [∀ v, Fintype (Q v)] where
  ops : List (SparseOp M L Q)
  mc : (v : Fin M) → Q v → Q v → Q v → L v
  mQ : (v : Fin M) → Q v → Q v → Q v → Q v
  m_maltsev : ∀ (v : Fin M) (x y : L v × Q v),
    (x.1 - y.1 + y.1 + mc v x.2 y.2 y.2, mQ v x.2 y.2 y.2) = x ∧
    (x.1 - x.1 + y.1 + mc v x.2 x.2 y.2, mQ v x.2 x.2 y.2) = y
  H : Set (RowTuple M L Q)
  H_nonempty : H.Nonempty

namespace CentralSetting

variable {M : ℕ} {L Q : Fin M → Type} [∀ v, AddCommGroup (L v)] [∀ v, Fintype (L v)]
  [∀ v, Fintype (Q v)]

/-- The rowwise Mal'tsev operation `m`: at row `v`,
`m((ℓ₁,q₁),(ℓ₂,q₂),(ℓ₃,q₃)) = (ℓ₁ − ℓ₂ + ℓ₃ + mc_v(q₁,q₂,q₃), mQ_v(q₁,q₂,q₃))`. -/
def m (S : CentralSetting M L Q) (x y z : RowTuple M L Q) : RowTuple M L Q :=
  fun v => ((x v).1 - (y v).1 + (z v).1 + S.mc v (x v).2 (y v).2 (z v).2,
    S.mQ v (x v).2 (y v).2 (z v).2)

/-- Membership in `T = Sg(H)`, generated by the sparse operations and `m`. -/
inductive InT (S : CentralSetting M L Q) : RowTuple M L Q → Prop where
  | gen {h : RowTuple M L Q} : h ∈ S.H → InT S h
  | op (f : SparseOp M L Q) : f ∈ S.ops → ∀ x : Fin f.arity → RowTuple M L Q,
      (∀ k, InT S (x k)) → InT S (f.eval x)
  | mal (x y z : RowTuple M L Q) : InT S x → InT S y → InT S z → InT S (S.m x y z)

/-- `T = Sg(H)`. -/
def T (S : CentralSetting M L Q) : Set (RowTuple M L Q) := {t | InT S t}

/-- The quotient projection `π = (π_v)_v`, `π_v(ℓ, u) = u`. -/
def pi (_S : CentralSetting M L Q) (x : RowTuple M L Q) : (v : Fin M) → Q v :=
  fun v => (x v).2

/-- The central translation `x + d` of a tuple by `d ∈ ∏_v L_v`. -/
def translate (_S : CentralSetting M L Q) (x : RowTuple M L Q) (d : (v : Fin M) → L v) :
    RowTuple M L Q :=
  fun v => ((x v).1 + d v, (x v).2)

end CentralSetting

end UniformSubpower.Supplied


