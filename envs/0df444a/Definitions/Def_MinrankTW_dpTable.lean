-- Prove2me | Definitions.Def_MinrankTW_dpTable
-- name    : MinrankTW_dpTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:59.572994+00:00
-- url     : https://prove2.me/theorems/e5989132-9242-4d17-8b40-23ca73767fcc
-- title:
--   Dynamic-programming tables $F_t(R,z)$
-- statement:
--   For entry constraints $S$ and a nice decomposition, the tables $F_t(R,z)$ are defined from the leaves to the root:
--
--   1. at an empty leaf, $F_t(\{0\},z)=1$ and every other entry is $0$;
--   2. at a node with one child $u$, $z^{\delta}F_u(R,z)$ is added to $F_t(R',z)$ for every child state $R$, where $R'$ is the relation update and $\delta$ the rank increment: $\delta=0$ for introductions and entry assignments, $\delta=\dim R(0)-\dim R'(0)$ when forgetting a row and $\delta=1+\dim\mathrm{dom}\,R'-\dim\mathrm{dom}\,R$ when forgetting a column;
--   3. at an entry introduction this is done for every allowed value $\alpha\in S_{ij}$ and the contributions are added;
--   4. at a join, $F_t$ is the join convolution (10) of the children's tables.
--
--   Eq. (14) identifies $F_t(R,z)$ with the sum of $z^{\operatorname{rank}M_t[I_t,I_t]}$ over the partial assignments with relation $R$.
--
--   **Formalization Note** Relations are in ambient coordinates; the increments are computed in $\mathbb N$, where on the relations the recursion reaches they equal the source's values in $\{0,1\}$.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 3.3, pp.11–12

import Mathlib
import Definitions.Def_MinrankTW_LinRel
import Definitions.Def_MinrankTW_NiceTree
import Definitions.Def_MinrankTW_relUpdate
import Definitions.Def_MinrankTW_joinConv

namespace MinrankTW

open Polynomial

/-- The dynamic-programming tables `F_t(R, z)` (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §3.3, pp.11–12): at an empty leaf
`F_t({0}, z) = 1` (and `0` at every other relation); at a one-child node with child `u`,
`z^δ F_u(R, z)` is added to `F_t(R′, z)` for every child state `R`, where `R′` is the relation
update and `δ` the rank increment of §3.2 (p.11: `δ = 0` for introductions and entry
assignments, `δ = dim R(0) − dim R′(0)` when forgetting a row, `δ = 1 + dim dom R′ − dim dom R`
when forgetting a column); at an entry introduction this is done for every allowed value
`α ∈ S_ij` and the contributions are added; at a join the table is the convolution (10).

**Formalization Note** Relations are in ambient coordinates (`relOfPartial`), so the tables are
functions on all submodules of `F^n × F^m`; the sums over child states are `finsum`s over the
finitely many submodules. The increments are computed in `ℕ`; on the relations the recursion
reaches they are the paper's values in `{0, 1}`. Equality of submodules is decided
classically. -/
noncomputable def dpTable {F : Type*} [Field F] {m n : ℕ} (S : Fin m → Fin n → Finset F) :
    NiceTree m n → Submodule F ((Fin n → F) × (Fin m → F)) → ℕ[X]
  | .leaf => fun R => by classical exact if R = ⊥ then 1 else 0
  | .introRow i t => fun R' => ∑ᶠ (R : Submodule F ((Fin n → F) × (Fin m → F)))
      (_ : introRowRel i R = R'), dpTable S t R
  | .introCol j t => fun R' => ∑ᶠ (R : Submodule F ((Fin n → F) × (Fin m → F)))
      (_ : introColRel j R = R'), dpTable S t R
  | .assign i j t => fun R' => ∑ a ∈ S i j, ∑ᶠ (R : Submodule F ((Fin n → F) × (Fin m → F)))
      (_ : assignRel i j a R = R'), dpTable S t R
  | .forgetRow i t => fun R' => ∑ᶠ (R : Submodule F ((Fin n → F) × (Fin m → F)))
      (_ : forgetRowRel i R = R'),
      X ^ (Module.finrank F (relZero R) - Module.finrank F (relZero R')) * dpTable S t R
  | .forgetCol j t => fun R' => ∑ᶠ (R : Submodule F ((Fin n → F) × (Fin m → F)))
      (_ : forgetColRel j R = R'),
      X ^ (1 + Module.finrank F (relDom R') - Module.finrank F (relDom R)) * dpTable S t R
  | .join t₁ t₂ => joinConv (dpTable S t₁) (dpTable S t₂)

end MinrankTW


