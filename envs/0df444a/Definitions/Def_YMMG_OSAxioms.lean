-- Prove2me | Definitions.Def_YMMG_OSAxioms
-- name    : YMMG_OSAxioms
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T16:07:16.388405+00:00
-- url     : https://prove2.me/theorems/cba6a946-5aa3-40ac-a354-4e72e58a6bb5
-- title:
--   Osterwalder–Schrader axioms E0–E4 for Euclidean Green's functions
-- statement:
--   A **distribution family** is a sequence of continuous linear functionals $\mathfrak S_n$ on $\mathcal S(\mathbb R^{4n})$, for $n=0,1,2,\dots$. Osterwalder–Schrader take $\mathfrak S_n\in{}^0\mathcal S'(\mathbb R^{4n})$. Here $\mathfrak S_n$ is defined on all of $\mathcal S$, but every axiom only uses its values on ${}^0\mathcal S$. The axioms for a single hermitian scalar field (§3 of the paper) are:
--
--   - **E0**: $\mathfrak S_0=1$.
--   - **E1** (Euclidean invariance): $\mathfrak S_n(f)=\mathfrak S_n(f_{(a,R)})$ for all $R\in SO(4)$ and $a\in\mathbb R^4$.
--   - **E2** (reflection positivity): $\sum_{n,m}\mathfrak S_{n+m}(\Theta f_n^*\times f_m)\ge0$ for terminating sequences with $f_n\in\mathcal S_+$.
--   - **E3** (symmetry) under permutations of the points.
--   - **E4** (cluster property) under spatial translations.
--
--   Transformed test functions are specified pointwise.
-- source:
--   K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's Functions*, Commun. Math. Phys. 31, 83–112 (1973), https://doi.org/10.1007/BF01645738, §2 (involutions Θ, *, product ×) and §3 (axioms E0–E4)

module

public import Mathlib
public import Definitions.Def_YMMG_Spacetime

/-!
# Osterwalder–Schrader axioms (Osterwalder–Schrader 1973, §2–§3)

A *Schwinger family* is a sequence `𝔖ₙ`, `n = 0, 1, 2, …`, of continuous linear functionals on
the Schwartz spaces `𝒮(ℝ⁴ⁿ)`.  Osterwalder and Schrader take `𝔖ₙ ∈ ⁰𝒮'(ℝ⁴ⁿ)`, i.e. continuous
functionals on the closed subspace `⁰𝒮(ℝ⁴ⁿ)` of Schwartz functions vanishing with all derivatives
at coinciding points.  Here `𝔖ₙ` is given on all of `𝒮(ℝ⁴ⁿ)` (every element of `⁰𝒮'` has such a
continuous extension, by Hahn–Banach), and **every axiom only uses the values of `𝔖ₙ` on
`⁰𝒮(ℝ⁴ⁿ)`**; the values off `⁰𝒮` are irrelevant junk.

The axioms are stated for a single hermitian scalar field, as in §3 of the paper.
Transformed test functions (`f_{(a,R)}`, `f^π`, `Θf*`, `f × g`) are not constructed; instead the
axioms quantify over every Schwartz function that agrees pointwise with the transformed function
(such a Schwartz function always exists and is unique).
-/

@[expose] public section

noncomputable section

namespace YangMillsMassGap

open scoped ComplexOrder
open Filter Topology

/-- A sequence of continuous linear functionals `𝔖ₙ` on `𝒮(ℝ⁴ⁿ)` (Euclidean Green's functions /
Schwinger functions) or `𝔚ₙ` (Wightman distributions). -/
abbrev DistributionFamily := (n : ℕ) → SchwartzMap (Config n) ℂ →L[ℂ] ℂ

/-- The first `n` points of an `(n+m)`-point configuration. -/
def Config.fst {n m : ℕ} (x : Config (n + m)) : Config n :=
  Config.mk (fun i => x.pt (Fin.castAdd m i))

/-- The last `m` points of an `(n+m)`-point configuration. -/
def Config.snd {n m : ℕ} (x : Config (n + m)) : Config m :=
  Config.mk (fun j => x.pt (Fin.natAdd n j))

/-- `(ϑxₙ, …, ϑx₁)`: reverse the order of the points and reflect time in each point. This is the
argument of `(Θf*)ₙ(x₁,…,xₙ) = conj fₙ(ϑxₙ, …, ϑx₁)`. -/
def Config.reflectReverse {n : ℕ} (x : Config n) : Config n :=
  Config.mk (fun i => timeReflect (x.pt (Fin.rev i)))

/-- Apply the Euclidean motion `x ↦ R x + a` to every point. -/
def Config.euclidMove {n : ℕ} (R : Matrix (Fin 4) (Fin 4) ℝ) (a : Spacetime) (x : Config n) :
    Config n :=
  Config.mk (fun i => matAct R (x.pt i) + a)

/-- `(x_{π(1)}, …, x_{π(n)})`. -/
def Config.permute {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n) : Config n :=
  Config.mk (fun i => x.pt (π i))

/-- `h = Θfₙ* × gₘ` pointwise: `h(x₁,…,x_{n+m}) = conj fₙ(ϑxₙ,…,ϑx₁) · gₘ(x_{n+1},…,x_{n+m})`. -/
def IsThetaStarTimes {n m : ℕ} (f : SchwartzMap (Config n) ℂ) (g : SchwartzMap (Config m) ℂ)
    (h : SchwartzMap (Config (n + m)) ℂ) : Prop :=
  ∀ x : Config (n + m), h x = (starRingEnd ℂ) (f x.fst.reflectReverse) * g x.snd

/-- `k = Θfₙ*` pointwise: `k(x₁,…,xₙ) = conj fₙ(ϑxₙ,…,ϑx₁)`. -/
def IsThetaStar {n : ℕ} (f k : SchwartzMap (Config n) ℂ) : Prop :=
  ∀ x : Config n, k x = (starRingEnd ℂ) (f x.reflectReverse)

/-- **E0** (distributions): `𝔖₀ = 1`, i.e. `𝔖₀(f) = f(pt)` on the one-point space `ℝ⁰`. -/
def OS_E0 (S : DistributionFamily) : Prop :=
  ∀ f : SchwartzMap (Config 0) ℂ, S 0 f = f 0

/-- **E1** (Euclidean invariance): `𝔖ₙ(f) = 𝔖ₙ(f_{(a,R)})` for all `R ∈ SO(4)`, `a ∈ ℝ⁴`,
`f ∈ ⁰𝒮(ℝ⁴ⁿ)`, where `f_{(a,R)}(x₁,…,xₙ) = f(Rx₁ + a, …, Rxₙ + a)`. -/
def OS_E1 (S : DistributionFamily) : Prop :=
  ∀ (n : ℕ) (R : Matrix (Fin 4) (Fin 4) ℝ) (a : Spacetime) (f g : SchwartzMap (Config n) ℂ),
    R ∈ rotationGroup → VanishesOnCoincidences f →
    (∀ x, g x = f (x.euclidMove R a)) → S n f = S n g

/-- **E2** (reflection positivity): `∑_{n,m} 𝔖_{n+m}(Θfₙ* × fₘ) ≥ 0` for every terminating
sequence `f = (f₀, f₁, …, f_N)` with `fₙ ∈ 𝒮₊(ℝ⁴ⁿ)`. (`≥ 0` in `ℂ` means real and non-negative.) -/
def OS_E2 (S : DistributionFamily) : Prop :=
  ∀ (N : ℕ) (f : (n : Fin (N + 1)) → SchwartzMap (Config n) ℂ)
    (h : (n m : Fin (N + 1)) → SchwartzMap (Config (n + m)) ℂ),
    (∀ n, IsPositiveTimeTest (f n)) → (∀ n m, IsThetaStarTimes (f n) (f m) (h n m)) →
    0 ≤ ∑ n : Fin (N + 1), ∑ m : Fin (N + 1), S ((n : ℕ) + m) (h n m)

/-- **E3** (symmetry): `𝔖ₙ(f) = 𝔖ₙ(f^π)` for all permutations `π` and all `f ∈ ⁰𝒮(ℝ⁴ⁿ)`,
where `f^π(x₁,…,xₙ) = f(x_{π(1)},…,x_{π(n)})`. -/
def OS_E3 (S : DistributionFamily) : Prop :=
  ∀ (n : ℕ) (π : Equiv.Perm (Fin n)) (f g : SchwartzMap (Config n) ℂ),
    VanishesOnCoincidences f → (∀ x, g x = f (x.permute π)) → S n f = S n g

/-- **E4** (cluster property): for terminating sequences `f, g` with entries in `𝒮₊` and every
spatial vector `a = (0, a⃗)`,
`lim_{λ→∞} ∑_{n,m} {𝔖_{n+m}(Θfₙ* × gₘ,(λa,1)) − 𝔖ₙ(Θfₙ*) 𝔖ₘ(gₘ)} = 0`,
where `gₘ,(λa,1)(x₁,…,xₘ) = gₘ(x₁ + λa, …, xₘ + λa)`. -/
def OS_E4 (S : DistributionFamily) : Prop :=
  ∀ (N : ℕ) (f g : (n : Fin (N + 1)) → SchwartzMap (Config n) ℂ) (a : Space)
    (k : (n : Fin (N + 1)) → SchwartzMap (Config n) ℂ)
    (gt : ℝ → (m : Fin (N + 1)) → SchwartzMap (Config m) ℂ)
    (h : ℝ → (n m : Fin (N + 1)) → SchwartzMap (Config (n + m)) ℂ),
    (∀ n, IsPositiveTimeTest (f n)) → (∀ n, IsPositiveTimeTest (g n)) →
    (∀ n, IsThetaStar (f n) (k n)) →
    (∀ t m x, gt t m x = g m (x.euclidMove 1 (t • ofSpace a))) →
    (∀ t n m, IsThetaStarTimes (f n) (gt t m) (h t n m)) →
    Tendsto (fun t : ℝ => ∑ n : Fin (N + 1), ∑ m : Fin (N + 1),
        (S ((n : ℕ) + m) (h t n m) - S n (k n) * S m (g m)))
      atTop (𝓝 0)

/-- A family of Euclidean Green's functions satisfying the Osterwalder–Schrader axioms
`E0`–`E4` of Osterwalder–Schrader (1973), §3. -/
structure SatisfiesOSAxioms (S : DistributionFamily) : Prop where
  e0 : OS_E0 S
  e1 : OS_E1 S
  e2 : OS_E2 S
  e3 : OS_E3 S
  e4 : OS_E4 S

end YangMillsMassGap

end


