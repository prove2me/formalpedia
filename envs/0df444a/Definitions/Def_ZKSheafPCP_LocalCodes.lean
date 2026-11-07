-- Prove2me | Definitions.Def_ZKSheafPCP_LocalCodes
-- name    : ZKSheafPCP_LocalCodes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:10:27.788205+00:00
-- url     : https://prove2.me/theorems/dcf2defd-af9e-446a-9a81-a12863986ab0
-- title:
--   Sheaf codes, local sections, extendability and MDS codes
-- statement:
--   A **sheaf of linear codes** on a coded space $P$ assigns to each $\sigma\in P$ a linear code $F_\sigma\subseteq\mathbb F^\sigma$, such that $c\in F_\sigma$ and $\tau\subseteq\sigma$ give $c|_\tau\in F_\tau$. For an upper set $U$, the **local section** is $F(U)=\{c\in\mathbb F^{P_U}:c|_\sigma\in F_\sigma\ \forall\sigma\in U\}$.
--
--   $U$ is **extendable** to $V$ if each $f\in F(U)$ is the restriction of some $g\in F(V)$, **uniquely extendable** if that $g$ is unique, and **globally extendable** if it is extendable to $P$. The **extension code** is $F_{W=d}(V)=\{c\in F(V):c|_{P_V\cap P_W}=d|_{P_V\cap P_W}\}$. $S$ is a **$\kappa$-extendable cover** for $F_{W=d}$ if it is a cover and for each $S'\subseteq S$ with $|S'|\le\kappa$, $U_{S'}$ is globally extendable with respect to $F_{W=d}$.
--
--   A linear code $C$ on $\rho$ is **MDS** if every nonzero word has weight at least $|\rho|-\dim C+1$. $\Delta(f|_\rho,C)$ is the fractional Hamming distance to $C$.
--
--   **Formalization Note** A local code is stored zero-padded as a subspace of $\mathbb F^D$; padding preserves dimension (Corollary 3.11). The zero code counts as MDS. For a nonzero code, the Singleton bound makes this the same as $\Delta_C=|D|-\dim C+1$.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definitions 3.17, 4.8, 4.10, 6.3, 6.4, pp.12–26

import Mathlib
import Definitions.Def_ZKSheafPCP_CodedSpace

namespace ZKSheafPCP

open Classical

/-- The local codes of a sheaf code on a domain `D` (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission,
manuscript sha256 ac5e528f…, Definition 4.8, p.15).

**Formalization Note** A local code `F_σ ⊆ 𝔽^σ` is stored in its zero-padded form (Definition 3.9, p.11), a subspace
of `D → 𝔽`. Padding is a linear bijection and preserves dimension (Claim 3.10, Corollary 3.11). Only the values at
members of the coded space matter. -/
structure LocalCodes (F D : Type) [Field F] where
  /-- the local code at `σ` -/
  code : Finset D → Submodule F (D → F)

namespace LocalCodes

variable {F D : Type} [Field F] (𝓕 : LocalCodes F D) (PP : CodedSpace D)

/-- Sheaf of linear codes (Definition 4.8, p.15): each `F_σ` lives on `σ`, and `c ∈ F_σ`, `σ ⩽ τ` give
`c|_τ ∈ F_τ`. -/
def IsSheaf : Prop :=
  (∀ σ ∈ PP.P, ∀ c ∈ 𝓕.code σ, ∀ x, x ∉ σ → c x = 0) ∧
  ∀ σ ∈ PP.P, ∀ τ ∈ PP.P, τ ⊆ σ → ∀ c ∈ 𝓕.code σ, restr τ c ∈ 𝓕.code τ

/-- The local section `F(U)` (Definition 4.8, p.15), zero-padded: the words on `P_U` whose restriction to each
`σ ∈ U` lies in `F_σ`. -/
def sections (U : Finset (Finset D)) : Set (D → F) :=
  {c | (∀ x, x ∉ supp U → c x = 0) ∧ ∀ σ ∈ U, restr σ c ∈ 𝓕.code σ}

/-- `U` is extendable to `V` (Definition 4.10, p.15): every `f ∈ F(U)` is the restriction of some `g ∈ F(V)`. -/
def Extendable (U V : Finset (Finset D)) : Prop :=
  ∀ f ∈ 𝓕.sections U, ∃ g ∈ 𝓕.sections V, restr (supp U) g = f

/-- `U` is uniquely extendable to `V` (Definition 4.10, p.15): every `f ∈ F(U)` has exactly one extension. -/
def UniquelyExtendable (U V : Finset (Finset D)) : Prop :=
  ∀ f ∈ 𝓕.sections U, ∃! g, g ∈ 𝓕.sections V ∧ restr (supp U) g = f

/-- `U` is globally extendable (Definition 4.10, p.15). -/
def GloballyExtendable (U : Finset (Finset D)) : Prop :=
  𝓕.Extendable U PP.P

/-- `F_{W=d}(V)` of the extension sheaf code (Definition 6.4, p.26): the `c ∈ F(V)` agreeing with `d` on
`P_V ∩ P_W`. It is an affine subset, not a subspace. -/
def relSections (W : Finset (Finset D)) (d : D → F) (V : Finset (Finset D)) : Set (D → F) :=
  {c | c ∈ 𝓕.sections V ∧ restr (supp V ∩ supp W) c = restr (supp V ∩ supp W) d}

/-- `A` is globally extendable with respect to the extension sheaf code `F_{W=d}` (Definitions 4.10 and 6.4): each
element of `F_{W=d}(A)` is the restriction of an element of `F_{W=d}(P)`. -/
def RelGloballyExtendable (W : Finset (Finset D)) (d : D → F) (A : Finset (Finset D)) : Prop :=
  ∀ f ∈ 𝓕.relSections W d A, ∃ g ∈ 𝓕.relSections W d PP.P, restr (supp A) g = f

/-- `S` is a `κ`-extendable cover with respect to `F_{W=d}` (Definition 6.3, p.26): `S` is a cover of `P`, and for
each `S' ⊆ S` with `|S'| ≤ κ`, `U_{S'}` is globally extendable with respect to `F_{W=d}`. -/
def IsRelKExtendableCover (κ : ℕ) (W : Finset (Finset D)) (d : D → F) (S : Finset (Finset D)) : Prop :=
  PP.IsCover S ∧
  ∀ S' ⊆ S, S'.card ≤ κ → 𝓕.RelGloballyExtendable PP W d (PP.closure S')

/-- The fractional Hamming distance from the word `f|_ρ` to the code `C` on `ρ` (§3.1, p.11). The set of
distances is nonempty, since `0 ∈ C`, and finite in value, so the infimum is attained. -/
noncomputable def distTo (ρ : Finset D) (f : D → F) (C : Submodule F (D → F)) : ℝ :=
  sInf {r : ℝ | ∃ c ∈ C, r = ((ρ.filter fun x => f x ≠ c x).card : ℝ) / ρ.card}

end LocalCodes

/-- A maximum distance separable code on `ρ` (Definition 3.17, p.12): every nonzero word has weight at least
`|ρ| - dim C + 1`.

**Formalization Note** Definition 3.17 reads `Δ_C = |D| - dim(C) + 1` with absolute distance. By the Singleton
bound `≥` is the same as `=` when `C ≠ 0`. The zero code has no minimum distance; it counts as MDS here. -/
def IsMDS {F D : Type} [Field F] (ρ : Finset D) (C : Submodule F (D → F)) : Prop :=
  ∀ c ∈ C, c ≠ 0 → ρ.card + 1 ≤ Module.finrank F C + (ρ.filter fun x => c x ≠ 0).card

end ZKSheafPCP


