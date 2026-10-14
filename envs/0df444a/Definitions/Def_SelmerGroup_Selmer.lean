-- Prove2me | Definitions.Def_SelmerGroup_Selmer
-- name    : SelmerGroup_Selmer
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T15:56:05.2479+00:00
-- url     : https://prove2.me/theorems/9686a6f4-002a-4af9-af54-f0329910de5b
-- title:
--   The $n$-Selmer group $\mathrm{Sel}^{(n)}(E/K)$ and $\text{Ш}(E/K)$
-- statement:
--   Let $E$ be a Weierstrass curve over a number field $K$ and $n\in\mathbb N$.
--
--   1. For a field $L\supseteq K$, a map $f:G_L\to E(\bar L)$ is a **Kummer cocycle** if there are $P\in E(L)$ and $Q\in E(\bar L)$ with $nQ=P$ and $f(\sigma)=\sigma Q-Q$ for all $\sigma\in G_L$. The **Kummer image** $\mathrm{im}\,\kappa_L\subseteq H^1(G_L,E(\bar L)[n])$ is the set of classes having a Kummer cocycle as representative, i.e. the image of $\kappa_L:E(L)/nE(L)\to H^1(G_L,E[n])$.
--   2. $j_L:H^1(G_L,E(\bar L)[n])\to H^1(G_L,E(\bar L))$ is induced by the inclusion $E[n]\subseteq E$.
--   3. The **$n$-Selmer group** $\mathrm{Sel}^{(n)}(E/K)\subseteq H^1(G_K,E(\bar K)[n])$ is the set of classes $\xi$ having a representative cocycle $c$ whose restriction to $G_{K_v}$ is a Kummer cocycle over $K_v$ for every finite place and every infinite place $v$ of $K$:
--   $$\mathrm{Sel}^{(n)}(E/K)=\bigcap_v\ker\big(H^1(G_K,E[n])\to H^1(G_{K_v},E[n])/\mathrm{im}\,\kappa_v\big).$$
--   4. The **Tate–Shafarevich group** $\text{Ш}(E/K)\subseteq H^1(G_K,E(\bar K))$ is the set of classes having a representative whose restriction to every $G_{K_v}$ is a coboundary $\sigma\mapsto\sigma R-R$ with $R\in E(\bar K_v)$; $\text{Ш}(E/K)[n]$ is its $n$-torsion.
--
--   These are the groups in the exact sequence $0\to E(K)/nE(K)\to\mathrm{Sel}^{(n)}(E/K)\to\text{Ш}(E/K)[n]\to0$.
--
--   **Formalization Note** Finite places are height-one primes of $\mathcal O_K$ with their adic completions; infinite places use `InfinitePlace.Completion`. The Selmer and Tate–Shafarevich groups are given as subsets. Asking for an exact Kummer cocycle at each place is equivalent to the coset condition, since $Q$ can be shifted by an $n$-torsion point.
-- source:
--   Wikipedia, "Selmer group", revision oldid=1370673670, https://en.wikipedia.org/w/index.php?title=Selmer_group&oldid=1370673670 , section "Selmer group of an isogeny" (p. 1 of the supplied PDF)

import Mathlib
import Definitions.Def_SelmerGroup_ContinuousH1
import Definitions.Def_SelmerGroup_GaloisPoints

/-!
# The `n`-Selmer group and the Tate–Shafarevich group of an elliptic curve

Let `E` be an elliptic curve over a number field `K` and `n ≥ 1`. The Selmer group of `E`
with respect to the isogeny `[n] : E → E` is
`Sel⁽ⁿ⁾(E/K) = ⋂_v ker (H¹(G_K, E[n]) → H¹(G_{K_v}, E[n]) / im κ_v)`,
`v` ranging over all places of `K` (finite and infinite), where
`κ_v : E(K_v)/nE(K_v) → H¹(G_{K_v}, E[n])` is the local Kummer map
`P ↦ [σ ↦ σ Q - Q]` for any `Q ∈ E(K̄_v)` with `n Q = P`.
-/

noncomputable section

open WeierstrassCurve NumberField

namespace SelmerGroup

variable {K : Type*} [Field K] (E : WeierstrassCurve K)

/-- `f : G_L → E(L̄)` is a Kummer cocycle for `[n]`: there are `P ∈ E(L)` and `Q ∈ E(L̄)`
with `n Q = P` and `f σ = σ Q - Q` for every `σ ∈ G_L`. -/
def IsKummerCocycle (L : Type*) [Field L] [Algebra K L] (n : ℕ)
    (f : Field.absoluteGaloisGroup L → Pts E (AlgebraicClosure L)) : Prop :=
  ∃ P : Pts E L, ∃ Q : Pts E (AlgebraicClosure L),
    n • Q = ptsMap E (IsScalarTower.toAlgHom K L (AlgebraicClosure L)) P ∧
    ∀ σ, f σ = absAct E L σ Q - Q

/-- `f : G_L → E(L̄)` is a coboundary: `f σ = σ R - R` for some `R ∈ E(L̄)`. -/
def IsCoboundary (L : Type*) [Field L] [Algebra K L]
    (f : Field.absoluteGaloisGroup L → Pts E (AlgebraicClosure L)) : Prop :=
  ∃ R : Pts E (AlgebraicClosure L), ∀ σ, f σ = absAct E L σ R - R

/-- The image of the Kummer map `κ_L : E(L)/nE(L) → H¹(G_L, E[n])`, as a subset of
`H¹(G_L, E(L̄)[n])`. -/
def kummerImage (L : Type*) [Field L] [Algebra K L] (n : ℕ) :
    Set (H1 (absTorsAct E L n)) :=
  {ξ | ∃ c : cocycles (absTorsAct E L n), H1.mk _ c = ξ ∧
    IsKummerCocycle E L n (fun σ => (c.1 σ : Pts E (AlgebraicClosure L)))}

/-- The map `H¹(G_L, E[n]) → H¹(G_L, E)` induced by the inclusion `E(L̄)[n] ⊆ E(L̄)`. -/
def torsInclH1 (L : Type*) [Field L] [Algebra K L] (n : ℕ) :
    H1 (absTorsAct E L n) →+ H1 (absAct E L) :=
  H1.map (absTorsAct E L n) (absAct E L) (tors E (AlgebraicClosure L) n).subtype
    (fun _ _ => rfl)

/-- The `n`-Selmer group `Sel⁽ⁿ⁾(E/K) ⊆ H¹(G_K, E[n])`: classes whose restriction to every
completion `K_v` (finite places `v` and infinite places `w`) lies in the image of the local
Kummer map. -/
def selmerGroup [NumberField K] (n : ℕ) : Set (H1 (absTorsAct E K n)) :=
  {ξ | ∃ c : cocycles (absTorsAct E K n), H1.mk _ c = ξ ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsKummerCocycle E (v.adicCompletion K) n
        (localize E (v.adicCompletion K) (fun σ => (c.1 σ : Pts E (AlgebraicClosure K))))) ∧
    (∀ w : InfinitePlace K,
      IsKummerCocycle E w.Completion n
        (localize E w.Completion (fun σ => (c.1 σ : Pts E (AlgebraicClosure K)))))}

/-- The Tate–Shafarevich group `Ш(E/K) ⊆ H¹(G_K, E(K̄))`: classes whose restriction to every
completion `K_v` is trivial. -/
def sha [NumberField K] : Set (H1 (absAct E K)) :=
  {ξ | ∃ c : cocycles (absAct E K), H1.mk _ c = ξ ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      IsCoboundary E (v.adicCompletion K) (localize E (v.adicCompletion K) c.1)) ∧
    (∀ w : InfinitePlace K, IsCoboundary E w.Completion (localize E w.Completion c.1))}

/-- The `n`-torsion `Ш(E/K)[n]` of the Tate–Shafarevich group. -/
def shaTors [NumberField K] (n : ℕ) : Set (H1 (absAct E K)) :=
  {ξ | ξ ∈ sha E ∧ n • ξ = 0}

end SelmerGroup


