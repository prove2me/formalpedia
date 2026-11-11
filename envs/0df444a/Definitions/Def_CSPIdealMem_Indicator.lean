-- Prove2me | Definitions.Def_CSPIdealMem_Indicator
-- name    : CSPIdealMem_Indicator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:28:51.639723+00:00
-- url     : https://prove2.me/theorems/1e1e7843-4205-482c-bec5-aeabc94919eb
-- title:
--   Indicator coordinates $B_d$, $\eta_d$, $V_d(R)$, the multilinear extension $T_t$, absorbing subspaces and the local spaces $V_S$, $V_{S,T}$
-- statement:
--   Let $X=\{x_1,\dots,x_n\}$ and $S_d=\{S\subseteq X: |S|\le d\}$. Put
--   $$
--   B_d=\prod_{S\in S_d}\mathbb Q^{D^S},
--   $$
--   with coordinates $z_{S,a}$ ($S\in S_d$, $a\in D^S$) and standard basis vectors $e_a$ in each block. For $\varphi\in D^X$, the **indicator evaluation vector** $\eta_d(\varphi)$ has $\eta_d(\varphi)_{S,a}=1$ if $\varphi|_S=a$ and $0$ otherwise; for $R\subseteq D^X$, $V_d(R)=\mathrm{span}_{\mathbb Q}\{\eta_d(\varphi)\mid\varphi\in R\}$.
--
--   For $t:D^k\to D$, the **blockwise multilinear extension** $T_t:B_d^k\to B_d$ is, on each block, the unique multilinear map with $T_{t,S}(e_{a_1},\dots,e_{a_k})=e_{t(a_1,\dots,a_k)}$; explicitly
--   $$
--   T_t(z_1,\dots,z_k)_{S,b}=\sum_{\substack{a_1,\dots,a_k\in D^S\\ t(a_1,\dots,a_k)=b}}\ \prod_{j=1}^k (z_j)_{S,a_j}.
--   $$
--   A subspace $H\subseteq B_d$ is **closed under** $T_t$ if $T_t(h_1,\dots,h_k)\in H$ for all $h_j\in H$; a subspace $J\subseteq H$ is **absorbing** if $T_t(h_1,\dots,h_k)\in J$ whenever all $h_j\in H$ and at least one $h_j\in J$. $H\cap\mathbb Z^N$ is the set of integral vectors of $H$.
--
--   With $\pi_SR=\{\varphi|_S:\varphi\in R\}$, the **local spaces** are $V_S(R)=\mathrm{span}_{\mathbb Q}\{e_a\mid a\in\pi_SR\}$ and $V_{S,T}(R)=\mathrm{span}_{\mathbb Q}\{(e_{a|_S},e_{a|_T})\mid a\in\pi_{S\cup T}R\}$.
--
--   These are the objects of the local reconstruction theorem (§3).
--
--   **Formalization Note** Blocks are indexed by `Finset (Fin n)` of size $\le d$; a block is the space of functions on assignments $S\to D$; the domain is any finite type. The generators of $V_{S,T}(R)$ are written $(e_{\varphi|_S},e_{\varphi|_T})$ for $\varphi\in R$, the same set.
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), S_d, B_d, η_d, V_d(R), p.14 (PDF 14); T_t, p.15 (PDF 15); closure and H ∩ Z^N, p.17 (PDF 17); absorbing subspaces, p.18 (PDF 18); π_S R, p.5 (PDF 5); V_S, V_{S,T}, p.21 (PDF 21)

import Mathlib
import Definitions.Def_CSPIdealMem_Polymorphism

namespace CSPIdealMem

/-! # Indicator coordinates and blockwise multilinear extensions of operations

Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109): `S_d`, `B_d`, `η_d`, `V_d(R)`,
p.14 (PDF 14); the blockwise multilinear extension `T_t`, p.15 (PDF 15); linear subalgebras,
p.17 (PDF 17); `H ∩ ℤ^N`, p.17; absorbing subspaces, p.18 (PDF 18); the projections `π_S R`,
p.5 (PDF 5); the local spaces `V_S(R)`, `V_{S,T}(R)`, p.21 (PDF 21).

**Formalization Note.** The variables are `X = Fin n` and the domain is a finite type `α`
(for the paper's `D ⊆ ℚ`, `α := ↥D`; nothing here depends on the labels). A block index
`S ∈ S_d` is a `Finset (Fin n)` of size `≤ d`; the block `ℚ^{D^S}` is the space of functions
`(↥S → α) → ℚ`, and `B_d = ∏_{S ∈ S_d} ℚ^{D^S}` is the dependent function space. The standard
basis vector `e_a` is `Pi.single a 1`. -/

open Classical

variable {α : Type}

/-- `S_d := {S ⊆ X | |S| ≤ d}` (p.14), for `X = Fin n`. -/
abbrev Sd (n d : ℕ) : Type := {S : Finset (Fin n) // S.card ≤ d}

/-- `B_d := ∏_{S ∈ S_d} ℚ^{D^S}` (p.14): one block of coordinates `z_{S,a}`, `a ∈ D^S`, for each
`S ∈ S_d`. -/
abbrev Bd (α : Type) (n d : ℕ) : Type := (S : Sd n d) → ((↥S.1 → α) → ℚ)

/-- The restriction `φ|_S` of an assignment to `S ⊆ X`. -/
def restr {n : ℕ} (S : Finset (Fin n)) (φ : Fin n → α) : ↥S → α :=
  fun x => φ x

/-- The projection `π_S R := {φ|_S | φ ∈ R} ⊆ D^S` (p.5). -/
def proj {n : ℕ} (S : Finset (Fin n)) (R : Set (Fin n → α)) : Set (↥S → α) :=
  restr S '' R

/-- The indicator evaluation vector `η_d(φ) ∈ B_d` (p.14): `η_d(φ)_{S,a} = 1` if `φ|_S = a` and
`0` otherwise. -/
noncomputable def eta {n : ℕ} (d : ℕ) (φ : Fin n → α) : Bd α n d :=
  fun S a => if restr S.1 φ = a then 1 else 0

/-- The indicator evaluation space `V_d(R) := span_ℚ {η_d(φ) | φ ∈ R}` (p.14). -/
noncomputable def V {n : ℕ} (d : ℕ) (R : Set (Fin n → α)) : Submodule ℚ (Bd α n d) :=
  Submodule.span ℚ (eta d '' R)

/-- The blockwise multilinear extension `T_t : B_d^k → B_d` of `t : α^k → α` (p.15). On the block
`S` it is the unique map `T_{t,S}`, multilinear in its `k` inputs, with
`T_{t,S}(e_{a_1}, …, e_{a_k}) = e_{t(a_1, …, a_k)}` (`t` acting coordinatewise on `a_j : S → α`);
expanding each input in the standard basis gives the explicit formula
`T_t(z_1, …, z_k)_{S,b} = ∑_{a_1, …, a_k ∈ D^S, t(a_1, …, a_k) = b} ∏_j (z_j)_{S,a_j}`. -/
noncomputable def Tt [Fintype α] {n d k : ℕ} (t : (Fin k → α) → α) (z : Fin k → Bd α n d) :
    Bd α n d :=
  fun S b => ∑ a : Fin k → (↥S.1 → α),
    if (fun x => t (fun j => a j x)) = b then ∏ j, z j S (a j) else 0

/-- `H` is closed under `T_t` (p.17): `T_t(h_1, …, h_k) ∈ H` whenever `h_1, …, h_k ∈ H`. -/
def ClosedUnder [Fintype α] {n d k : ℕ} (t : (Fin k → α) → α) (H : Submodule ℚ (Bd α n d)) :
    Prop :=
  ∀ h : Fin k → Bd α n d, (∀ j, h j ∈ H) → Tt t h ∈ H

/-- `J ⊆ H` is absorbing for `T_t` (p.18): `T_t(h_1, …, h_k) ∈ J` whenever all inputs belong to
`H` and at least one input belongs to `J`. -/
def Absorbing [Fintype α] {n d k : ℕ} (t : (Fin k → α) → α) (H J : Submodule ℚ (Bd α n d)) :
    Prop :=
  J ≤ H ∧ ∀ h : Fin k → Bd α n d, (∀ j, h j ∈ H) → (∃ j, h j ∈ J) → Tt t h ∈ J

/-- `z ∈ ℤ^N` (p.17): every coordinate of `z` is an integer. -/
def IsIntegral {n d : ℕ} (z : Bd α n d) : Prop :=
  ∀ S a, ∃ m : ℤ, z S a = m

/-- The one-block space `V_S(R) := span_ℚ {e_a | a ∈ π_S R}` (p.21). -/
noncomputable def VS {n d : ℕ} (R : Set (Fin n → α)) (S : Sd n d) :
    Submodule ℚ ((↥S.1 → α) → ℚ) :=
  Submodule.span ℚ ((fun a => Pi.single a (1 : ℚ)) '' proj S.1 R)

/-- The two-block space `V_{S,T}(R) := span_ℚ {(e_{a|S}, e_{a|T}) | a ∈ π_{S∪T} R}` (p.21). Since
the restrictions of `a = φ|_{S∪T}` to `S` and `T` are `φ|_S` and `φ|_T`, the generators are
`(e_{φ|S}, e_{φ|T})` for `φ ∈ R`. -/
noncomputable def VST {n d : ℕ} (R : Set (Fin n → α)) (S T : Sd n d) :
    Submodule ℚ (((↥S.1 → α) → ℚ) × ((↥T.1 → α) → ℚ)) :=
  Submodule.span ℚ
    ((fun φ => (Pi.single (restr S.1 φ) (1 : ℚ), Pi.single (restr T.1 φ) (1 : ℚ))) '' R)

end CSPIdealMem


