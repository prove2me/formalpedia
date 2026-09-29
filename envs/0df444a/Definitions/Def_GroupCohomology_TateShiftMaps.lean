-- Prove2me | Definitions.Def_GroupCohomology_TateShiftMaps
-- name    : GroupCohomology_TateShiftMaps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/3f17d26f-3bc3-54dd-8528-8eb997cfcb39
-- title:
--   Induced maps and connecting maps on Tate cohomology
-- statement:
--   Over a commutative ring $k$ and a finite group $G$, the $\mathbb Z$-graded object $A \mapsto A.\mathtt{tateCohomology}$ is assembled piecewise: in degrees $n \ge 1$ it is Mathlib's group cohomology $H^n(G,A)$, in degree $0$ it is $A^G$ modulo the image of the map $\bar N$ induced by the norm $\sum_{g} \rho(g)$ on coinvariants, in degree $-1$ it is $\ker \bar N$, and in degree $-(m+2)$ for $m \ge 0$ it is group homology $H_{m+1}(G,A)$. This module supplies the two pieces of data accompanying that grading, both by case dispatch on the degree along the same pattern.
--
--   First, for a morphism $\varphi : A \to B$ of $k$-linear $G$-representations, [`Rep.tateMap`](../def/GroupCohomology_TateShiftMaps.html#L17) gives a $k$-linear map in each degree $n$: for $n = m+1 \ge 1$ it is `groupCohomology.map` along the identity of $G$ in degree $m+1$; in degree $0$ it is the map on $A^G/\operatorname{im}\bar N$ induced by $\varphi$ on invariants; in degree $-1$ it is the map on $\ker\bar N$ induced by $\varphi$ on coinvariants; in degree $-(m+2)$ it is `groupHomology.map` along the identity of $G$ in degree $m+1$.
--
--   Second, for a short exact sequence $X$ of representations with proof `hX` of exactness, [`Rep.tateδ`](../def/GroupCohomology_TateShiftMaps.html#L32) gives connecting maps $\hat H^n(X_3) \to \hat H^{n+1}(X_1)$: for $n \ge 1$ the cohomological $\delta$ from degree $n$ to $n+1$; for $n = 0$ the map `tateδ₀`, the factorisation through $X_3^G/\operatorname{im}\bar N$ of $\delta^0$ precomposed with the inverse of the degree‑$0$ comparison isomorphism; for $n = -1$ the map `tateδneg1`, obtained from norms of those elements $b \in X_2$ whose image in $X_3$ has vanishing norm, lifted back through the injection $X_1 \to X_2$; for $n = -2$ the map `tateδneg2`, the homological $\delta$ from $H_1$ to $H_0$ followed by the degree‑$0$ comparison isomorphism, corestricted to $\ker\bar N$; and for $n = -(m+3)$ the homological $\delta$ from $H_{m+2}$ to $H_{m+1}$.
--
--   Accompanying lemmas record the value of `tateMap` and of `tateδ` in each of these ranges of degrees as definitional identities.
--
--   **Relation to Mathlib.** Mathlib provides group cohomology and group homology of representations together with their induced maps and connecting maps, but no Tate cohomology of a finite group; the graded carrier and these maps on it are the project's own, built by splicing the Mathlib functors with the low-degree norm constructions.
--
--   **Where it is used.** These maps are the data on which the long exact sequence in all integer degrees, functoriality, naturality of $\delta$ and dimension shifting for Tate cohomology are stated and proved, providing the cohomological toolkit for the Galois-cohomological arguments used later.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_TateShiftMaps.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateSeam

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def tateMap {A B : Rep.{u} k G} (φ : A ⟶ B) : ∀ n : ℤ, (A.tateCohomology n ⟶ B.tateCohomology n)
  | (Int.ofNat (n + 1)) => groupCohomology.map (MonoidHom.id G) φ (n + 1)
  | (Int.ofNat 0) => ModuleCat.ofHom (tateH0Map φ)
  | (Int.negSucc 0) => ModuleCat.ofHom (tateHneg1Map φ)
  | (Int.negSucc (n + 1)) => groupHomology.map (MonoidHom.id G) φ (n + 1)

lemma tateMap_ofNat_succ {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) :
    tateMap φ (n + 1 : ℕ) = groupCohomology.map (MonoidHom.id G) φ (n + 1) := rfl
lemma tateMap_zero {A B : Rep.{u} k G} (φ : A ⟶ B) : tateMap φ 0 = ModuleCat.ofHom (tateH0Map φ) := rfl
lemma tateMap_neg_one {A B : Rep.{u} k G} (φ : A ⟶ B) : tateMap φ (-1) = ModuleCat.ofHom (tateHneg1Map φ) := rfl
lemma tateMap_negSucc_succ {A B : Rep.{u} k G} (φ : A ⟶ B) (n : ℕ) :
    tateMap φ (Int.negSucc (n + 1)) = groupHomology.map (MonoidHom.id G) φ (n + 1) := rfl

variable {X : ShortComplex (Rep.{u} k G)}

def tateδ (hX : X.ShortExact) : ∀ n : ℤ, (X.X₃.tateCohomology n ⟶ X.X₁.tateCohomology (n + 1))
  | (Int.ofNat (n + 1)) => groupCohomology.δ hX (n + 1) (n + 2) rfl
  | (Int.ofNat 0) => ModuleCat.ofHom (tateδ₀ hX)
  | (Int.negSucc 0) => ModuleCat.ofHom (tateδneg1 hX)
  | (Int.negSucc 1) => ModuleCat.ofHom (tateδneg2 hX)
  | (Int.negSucc (n + 2)) => groupHomology.δ hX (n + 2) (n + 1) rfl

lemma tateδ_ofNat_succ (hX : X.ShortExact) (n : ℕ) : tateδ hX (n + 1 : ℕ) = groupCohomology.δ hX (n + 1) (n + 2) rfl := rfl
lemma tateδ_zero (hX : X.ShortExact) : tateδ hX 0 = ModuleCat.ofHom (tateδ₀ hX) := rfl
lemma tateδ_neg_one (hX : X.ShortExact) : tateδ hX (-1) = ModuleCat.ofHom (tateδneg1 hX) := rfl
lemma tateδ_neg_two (hX : X.ShortExact) : tateδ hX (-2) = ModuleCat.ofHom (tateδneg2 hX) := rfl
lemma tateδ_negSucc_succ_succ (hX : X.ShortExact) (n : ℕ) :
    tateδ hX (Int.negSucc (n + 2)) = groupHomology.δ hX (n + 2) (n + 1) rfl := rfl

end Rep

end


