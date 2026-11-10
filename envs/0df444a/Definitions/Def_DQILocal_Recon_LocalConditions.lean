-- Prove2me | Definitions.Def_DQILocal_Recon_LocalConditions
-- name    : DQILocal_Recon_LocalConditions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:04:59.32262+00:00
-- url     : https://prove2.me/theorems/9ef66a23-d4e4-4fee-b18e-3230bb3abc33
-- title:
--   Regular instances, the code $C$, the factor graph, balls $N_t(i),F_t(i),L_t(i)$ and the local conditions $\mathrm{LT}_t(i)$, $\mathrm{TP}_t(i)$
-- statement:
--   An instance is a matrix $B\in\{0,1\}^{m\times n}$ read over $\mathbb Z_q$; its rows $j\in[m]$ are code **symbols** and its columns $a\in[n]$ are parity **checks**. $B$ is **$(k,D)$-regular** if every row has $k$ ones and every column has $D$ ones. The code is $C=\{c\in\mathbb Z_q^m:B^\top c=0\}$ and $K=\{Bz:z\in\mathbb Z_q^n\}$.
--
--   The **factor graph** $G_B$ is bipartite on symbols and checks, with an edge whenever $B_{ja}=1$. For a symbol $i$ and $t\ge0$:
--
--   1. $N_t(i)$ is the set of symbols at graph distance at most $2t$ from $i$;
--   2. $F_t(i)$ is the set of checks at distance at most $2t-1$ (empty for $t=0$);
--   3. $L_t(i)$ is the set of symbols at distance exactly $2t$;
--   4. $C_t(i)$ is the set of assignments on $N_t(i)$ that satisfy every check in $F_t(i)$.
--
--   The **local conditions** (Definition 3.5) are: $\mathrm{LT}_t(i)$, the ball of radius $2t$ around $i$ in $G_B$ is a tree; and $\mathrm{TP}_t(i)$, the restriction map $c\mapsto c|_{N_t(i)}$ sends $C$ onto $C_t(i)$.
--
--   Under both conditions a local estimate at $i$ is an estimate of the root of a tree code, which is how the paper reduces local decoding to tree decoding.
--
--   **Formalization Note** Entries of $B$ are `Bool`; checks are indexed by any finite type (`Fin n`, or (layer, block) for Gallager's ensemble). Distances are `SimpleGraph.edist` in $\mathbb N\cup\{\infty\}$, so symbols in other components are never in a ball; $F_t(i)$ is written as $\mathrm{dist}+1\le 2t$ to avoid natural-number subtraction. "The ball is a tree" is acyclicity of the subgraph induced on $N_t(i)\cup F_t(i)$ (it is connected through $i$). All codes are additive subgroups of $\mathbb Z_q^m$; $q$ need not be prime.
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), §3.1, p. 15; §3.2, p. 16; §3.4 and Definition 3.5, pp. 21–22

import Mathlib

namespace DQILocal.Recon

open scoped BigOperators

/-- **Regular instances.**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), §3.1, p. 15: "We say
that `B` is `(k, D)`-regular if every row has `k` ones and every column has `D` ones."

An instance is a 0/1 matrix `B` (entries `Bool`) whose rows `j ∈ Fin m` are the code symbols and
whose columns `a ∈ κ` are the parity checks (§3.2, p. 16).

**Formalization Note.** The check index set is any finite type `κ` (`Fin n` in the paper; Gallager's
ensemble indexes checks by (layer, block)). -/
def IsRegular {m : ℕ} {κ : Type} [Fintype κ] (k D : ℕ) (B : Matrix (Fin m) κ Bool) : Prop :=
  (∀ j, (Finset.univ.filter fun a => B j a = true).card = k) ∧
    (∀ a, (Finset.univ.filter fun j => B j a = true).card = D)

/-- `B` read over `ℤ_q` (`true ↦ 1`, `false ↦ 0`), p. 15. -/
def toZMod (q : ℕ) {m : ℕ} {κ : Type} (B : Matrix (Fin m) κ Bool) : Matrix (Fin m) κ (ZMod q) :=
  fun j a => if B j a then 1 else 0

/-- The code `C = K^⊥ = {c ∈ ℤ_q^m : Bᵀ c = 0}` (§3.2, p. 16). -/
def code (q : ℕ) {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) :
    Set (Fin m → ZMod q) :=
  {c | (toZMod q B).transpose.mulVec c = 0}

/-- `K = {Bz : z ∈ ℤ_q^n}` (§3.1, p. 15). -/
def imageK (q : ℕ) {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) :
    Set (Fin m → ZMod q) :=
  Set.range (toZMod q B).mulVec

/-- The factor graph `G_B` (§3.1, p. 15): bipartite on symbols `inl j` and checks `inr a`, with an
edge whenever `B_{ja} = 1`. -/
def factorGraph {m : ℕ} {κ : Type} (B : Matrix (Fin m) κ Bool) : SimpleGraph (Fin m ⊕ κ) :=
  SimpleGraph.fromRel fun u v => ∃ j a, u = Sum.inl j ∧ v = Sum.inr a ∧ B j a = true

/-- `N_t(i)`: the symbols at graph distance at most `2t` from `i` in `G_B` (§3.4, p. 21).

**Formalization Note.** Distances are `SimpleGraph.edist` (values in `ℕ∞`, `⊤` between different
components), so a symbol in another component is never in the ball. -/
noncomputable def ballSym {m : ℕ} {κ : Type} (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j => (factorGraph B).edist (Sum.inl i) (Sum.inl j) ≤ 2 * t

/-- `F_t(i)`: the checks at graph distance at most `2t - 1` from `i` (§3.4, p. 21); empty when
`t = 0`. Written `edist + 1 ≤ 2t` so that no natural-number subtraction occurs. -/
noncomputable def ballChk {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) (i : Fin m)
    (t : ℕ) : Finset κ := by
  classical
  exact Finset.univ.filter fun a => (factorGraph B).edist (Sum.inl i) (Sum.inr a) + 1 ≤ 2 * t

/-- `L_t(i)`: the symbols at graph distance exactly `2t` from `i` (§3.4, p. 21). -/
noncomputable def leaves {m : ℕ} {κ : Type} (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j => (factorGraph B).edist (Sum.inl i) (Sum.inl j) = 2 * t

/-- **`LT_t(i)` (local tree), Definition 3.5, p. 22**: the ball of radius `2t` around `i` in `G_B` is
a tree, i.e. the subgraph of `G_B` induced on `N_t(i) ∪ F_t(i)` is acyclic.

**Formalization Note.** Symbols are adjacent only to checks, so the vertices at distance at most
`2t` are exactly `N_t(i)` and `F_t(i)`; the induced subgraph is connected through `i`, so "is a
tree" is "is acyclic". -/
def LT {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ) : Prop :=
  ((factorGraph B).induce
    (Sum.inl '' (ballSym B i t : Set (Fin m)) ∪ Sum.inr '' (ballChk B i t : Set κ))).IsAcyclic

/-- The code `C_t(i)` of all assignments on `N_t(i)` that satisfy the checks in `F_t(i)`
(Definition 3.5, p. 22). -/
noncomputable def treeCode (q : ℕ) {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool)
    (i : Fin m) (t : ℕ) : Set (ballSym B i t → ZMod q) := by
  classical
  exact {y | ∀ a ∈ ballChk B i t,
    ∑ s : ballSym B i t, (if B s.1 a = true then y s else 0) = 0}

/-- **`TP_t(i)` (tree projection), Definition 3.5, p. 22**: the restriction map `c ↦ c|_{N_t(i)}`
sends `C` onto `C_t(i)` (the inclusion `C|_{N_t(i)} ⊆ C_t(i)` always holds, p. 22). -/
def TP (q : ℕ) {m : ℕ} {κ : Type} [Fintype κ] (B : Matrix (Fin m) κ Bool) (i : Fin m) (t : ℕ) :
    Prop :=
  ∀ y ∈ treeCode q B i t, ∃ c ∈ code q B, ∀ s : ballSym B i t, c s.1 = y s

end DQILocal.Recon


