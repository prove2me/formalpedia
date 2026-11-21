-- Prove2me | Definitions.Def_MasulloGRH_ExpDecaySpaces
-- name    : MasulloGRH_ExpDecaySpaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-20T21:26:10.260062+00:00
-- url     : https://prove2.me/theorems/496e2bb1-2fea-4ab0-b55c-4c57e10ba618
-- title:
--   Modulated groups, the spaces $\mathcal S_I(G)$ of Schwartz–Bruhat functions with $I$-exponential decay, and Schwartz–Bergman spaces $AS(\mathbb C_I)$
-- statement:
--   These are the two sides of the Mellin transform on a group with a module.
--
--   **Schwartz–Bergman spaces.** For $I\subset\mathbb R$ let $\mathbb C_I=\{s:\operatorname{Re}s\in I\}$. $\mathcal S(\mathbb C_I)$ is the space of functions $\phi$ holomorphic on $\mathbb C_I$ such that for every compact interval $[a,b]\subset I$ and every $N\ge0$ the function $s^N\phi(s)$ is bounded on $\mathbb C_{[a,b]}$. The **Schwartz–Bergman space** $AS(\mathbb C_I)$ is this space with the locally convex topology of the seminorms
--   $$\phi\mapsto\big\|(a+ix)^N\phi(a+ix)\big\|_{L^2(\mathbb R,dx)},\qquad a\in I,\ N\ge0 .$$
--
--   **Modulated groups.** A **module** on a locally compact abelian group $G$ is a non-trivial continuous proper homomorphism $|\cdot|_G\colon G\to\mathbb R_{>0}$; $G$ is **$\mathbb R_{>0}$-modulated** if the module is surjective.
--
--   **Exponential decay.** For a modulated group $(G,|\cdot|_G)$ and $I\subset\mathbb R$, $\mathcal S_I(G)$ is the space of continuous functions $\phi$ on $G$ with $|\cdot|_G^a\phi\in\mathcal S(G)$ for all $a\in I$. For a compact subgroup $k$ with compactly generated orthogonal, $\mathcal S_I(k,G)$ is the subspace of $k$-invariant functions, with the coarsest topology for which all maps
--   $$T_a\colon\mathcal S_I(k,G)\to\mathcal S(G/k),\qquad T_a(\phi)=|\cdot|_G^a\phi,\qquad a\in I,$$
--   are continuous. $\mathcal S_I(G)$ carries the **inductive topology**: the finest locally convex topology for which all inclusions $\mathcal S_I(k,G)\to\mathcal S_I(G)$ are continuous.
--
--   **The half-line.** $\mathbb R_{>0}$ is modulated by the identity; $\mathcal S_I(\mathbb R_{>0})$ is the space of smooth $\phi$ with $t^a\phi\in\mathcal S(\mathbb R_{>0})$ for $a\in I$, and the Mellin transform is $M(\phi)(s)=\int_0^\infty\phi(t)t^s\,dt/t$.
--
--   For $I=\mathbb R$ these are the functions with exponential decay, $\mathcal S_E(G)$. The $\theta$-functions of Schwartz–Bruhat functions in $\mathcal S_0(\mathbb A_F)$ lie in $\mathcal S_E(C_F)$.
--
--   **Formalization Note** A function on $\mathbb C_I$ is a function on $\mathbb C$ that vanishes outside $\mathbb C_I$. The source defines the topology of $AS(\mathbb C_I)$ with an exponent $1<p<\infty$ and a sequence $a_m\in I$ accumulating at both ends of $I$, and Lemma D.3.1.2 states that the topology does not depend on these choices; here $p=2$ and all $a\in I$ are used. The group $\mathbb R_{>0}$ is the multiplicative copy of $\mathbb R$ with $t=e^x$, so $M(\phi)(s)=\int_{\mathbb R}\phi(e^x)e^{sx}\,dx$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D: Definition D.2.1.1 (p. 793); Lemma D.3.1.2 and Definition D.3.1.3 (pp. 799–801); Definition D.3.2.1 (p. 801); Definitions D.3.3.1 and D.3.3.3 (pp. 804–805)

import Definitions.Def_MasulloGRH_SchwartzBruhat

/-!
# Modulated groups, Schwartz–Bruhat functions with I-exponential decay, Schwartz–Bergman spaces

Source: A. M. Masullo, *The Music of the Primes* (draft of 20 November 2026), Appendix D:
Definition D.2.1.1 (p. 793), Lemma D.3.1.2 and Definition D.3.1.3 (pp. 799–801),
Definition D.3.2.1 (p. 801), Definitions D.3.3.1 and D.3.3.3 (pp. 804–805).
-/

set_option warn.classDefReducibility false

namespace MasulloGRH

open Topology MeasureTheory

noncomputable section

universe u

/-! ### Schwartz–Bergman spaces -/

/-- The vertical strip `ℂ_I = {s : Re s ∈ I}` over a set `I ⊆ ℝ`. -/
def stripOver (I : Set ℝ) : Set ℂ := {s : ℂ | s.re ∈ I}

/-- `ϕ ∈ S(ℂ_I)` (Lemma D.3.1.2): `ϕ` is holomorphic on `ℂ_I` and Schwartz uniformly on the
vertical strips of bounded width inside `ℂ_I`: for every compact interval `[a, b] ⊆ I` and every
`N ≥ 0` the function `s^N ϕ(s)` is bounded on `ℂ_{[a,b]}`.  A function on `ℂ_I` is represented by
a function on `ℂ` that vanishes outside `ℂ_I`. -/
def IsUniformlySchwartzHolomorphic (I : Set ℝ) (ϕ : ℂ → ℂ) : Prop :=
  (∀ s : ℂ, s.re ∉ I → ϕ s = 0) ∧ DifferentiableOn ℂ ϕ (stripOver I) ∧
    ∀ a b : ℝ, Set.Icc a b ⊆ I → ∀ N : ℕ, ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖s ^ N * ϕ s‖ ≤ C

/-- The space `S(ℂ_I)` as a space of functions. -/
def schwartzBergmanSubmodule (I : Set ℝ) : Submodule ℂ (ℂ → ℂ) :=
  Submodule.span ℂ {ϕ | IsUniformlySchwartzHolomorphic I ϕ}

/-- The Schwartz–Bergman space `AS(ℂ_I)` (Definition D.3.1.3). -/
def SchwartzBergman (I : Set ℝ) : Type := ↥(schwartzBergmanSubmodule I)

instance (I : Set ℝ) : AddCommGroup (SchwartzBergman I) :=
  inferInstanceAs (AddCommGroup ↥(schwartzBergmanSubmodule I))

instance (I : Set ℝ) : Module ℂ (SchwartzBergman I) :=
  inferInstanceAs (Module ℂ ↥(schwartzBergmanSubmodule I))

/-- The underlying function of an element of `AS(ℂ_I)`. -/
def SchwartzBergman.toFun {I : Set ℝ} (ϕ : SchwartzBergman I) : ℂ → ℂ := ϕ.1

open Classical in
/-- The function `x ↦ (a + ix)^N ϕ(a + ix)` on the vertical line `Re s = a`, as an element of
`L²(ℝ)` (and `0` if it is not square integrable). -/
def SchwartzBergman.lineL2 {I : Set ℝ} (ϕ : SchwartzBergman I) (a : ℝ) (N : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  if h : MemLp (fun x : ℝ => (a + x * Complex.I) ^ N * ϕ.toFun (a + x * Complex.I)) 2 volume then
    h.toLp _
  else 0

/-- The topology of `AS(ℂ_I)` (Definition D.3.1.3): the locally convex topology of the seminorms
`‖(a + ix)^N ϕ(a + ix)‖_{L²(ℝ, dx)}` for `a ∈ I` and `N ≥ 0`, i.e. `L²`-convergence of all
`s^N ϕ` on all vertical lines of `ℂ_I`.  By Lemma D.3.1.2 this is the topology defined by any
exponent `p > 1` and any sequence `a_m ∈ I` accumulating at both ends of `I`. -/
instance (I : Set ℝ) : TopologicalSpace (SchwartzBergman I) :=
  ⨅ (a : ℝ) (_ : a ∈ I) (N : ℕ),
    TopologicalSpace.induced (fun ϕ : SchwartzBergman I => ϕ.lineL2 a N) inferInstance

/-! ### Modulated groups -/

section modulated

variable {G : Type u} [CommGroup G] [TopologicalSpace G]

/-- Definition D.2.1.1: `m` is a *module* on `G`: a non-trivial continuous proper homomorphism
`|·|_G : G → ℝ_{>0}`. -/
structure IsModule (m : G → ℝ) : Prop where
  pos : ∀ g, 0 < m g
  map_mul : ∀ g h, m (g * h) = m g * m h
  continuous : Continuous m
  proper : ∀ a b : ℝ, 0 < a → IsCompact (m ⁻¹' Set.Icc a b)
  nontrivial : ∃ g, m g ≠ 1

/-- The group is `ℝ_{>0}`-modulated by `m` (§3.1.1): `m` is a module and it is surjective onto
`ℝ_{>0}`. -/
def IsRposModule (m : G → ℝ) : Prop := IsModule m ∧ ∀ t : ℝ, 0 < t → ∃ g, m g = t

variable (G) [IsTopologicalGroup G]

/-- The space `S_I(G)` of Schwartz–Bruhat functions with `I`-exponential decay
(Definition D.3.3.1), as a space of functions: the continuous functions `ϕ` on `G` with
`|·|_G^a ϕ ∈ S(G)` for all `a ∈ I`. -/
def expDecaySubmodule (m : G → ℝ) (I : Set ℝ) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {ϕ | Continuous ϕ ∧
    ∀ a ∈ I, (fun g => ((m g ^ a : ℝ) : ℂ) * ϕ g) ∈ schwartzBruhatSubmodule G}

/-- The space `S_I(G)` of Schwartz–Bruhat functions with `I`-exponential decay on the modulated
group `(G, m)` (Definition D.3.3.1). -/
def ExpDecaySchwartz (m : G → ℝ) (I : Set ℝ) : Type u := ↥(expDecaySubmodule G m I)

instance (m : G → ℝ) (I : Set ℝ) : AddCommGroup (ExpDecaySchwartz G m I) :=
  inferInstanceAs (AddCommGroup ↥(expDecaySubmodule G m I))

instance (m : G → ℝ) (I : Set ℝ) : Module ℂ (ExpDecaySchwartz G m I) :=
  inferInstanceAs (Module ℂ ↥(expDecaySubmodule G m I))

variable {G}

/-- The underlying function of an element of `S_I(G)`. -/
def ExpDecaySchwartz.toFun {m : G → ℝ} {I : Set ℝ} (ϕ : ExpDecaySchwartz G m I) : G → ℂ := ϕ.1

instance (m : G → ℝ) (I : Set ℝ) : CoeFun (ExpDecaySchwartz G m I) (fun _ => G → ℂ) :=
  ⟨ExpDecaySchwartz.toFun⟩

open Classical in
/-- The operator `T_a : S_I(k, G) → S(G/k)`, `ϕ ↦ |·|_G^a ϕ` (D.3.3.2), for a subgroup `k`: the
function `|·|_G^a ϕ` viewed on `G/k` (it is `0` if that function is not Schwartz–Bruhat on
`G/k`). -/
def ExpDecaySchwartz.weighted {m : G → ℝ} {I : Set ℝ} (k : Subgroup G) (a : ℝ)
    (ϕ : ExpDecaySchwartz G m I) : SchwartzBruhat (G ⧸ k) :=
  if h : (fun x : G ⧸ k => ((m x.out ^ a : ℝ) : ℂ) * ϕ.toFun x.out) ∈
      schwartzBruhatSubmodule (G ⧸ k) then
    ⟨_, h⟩
  else 0

variable (G)

/-- The inductive topology of `S_I(G)` (Definition D.3.3.3): the finest locally convex topology
for which, for every compact subgroup `k` with compactly generated orthogonal, the inclusion of
the space `S_I(k, G)` of `k`-invariant elements is continuous, where `S_I(k, G)` carries the
projective topology of the operators `T_a : S_I(k, G) → S(G/k)`, `a ∈ I`. -/
instance (m : G → ℝ) (I : Set ℝ) : TopologicalSpace (ExpDecaySchwartz G m I) :=
  sInf {t | IsLocallyConvexTopology (ExpDecaySchwartz G m I) t ∧
    ∀ k : Subgroup G, IsGoodSubgroup k →
      @Continuous {ϕ : ExpDecaySchwartz G m I // ∀ h ∈ k, ∀ g : G, ϕ.toFun (g * h) = ϕ.toFun g}
        (ExpDecaySchwartz G m I)
        (⨅ (a : ℝ) (_ : a ∈ I),
          TopologicalSpace.induced (fun ϕ => ExpDecaySchwartz.weighted k a ϕ.1) inferInstance)
        t Subtype.val}

end modulated

/-- The module `x ↦ exp x` on the multiplicative group `ℝ_{>0}`, written as the multiplicative
copy of `ℝ` through `t = exp x`. -/
def rposModule (x : Multiplicative ℝ) : ℝ := Real.exp (Multiplicative.toAdd x)

/-- The space `S_I(ℝ_{>0})` of Schwartz–Bruhat functions on `ℝ_{>0}` with `I`-exponential decay
(Definition D.3.2.1); a function `ϕ` on `ℝ_{>0}` is the function `x ↦ ϕ(exp x)` on the
multiplicative copy of `ℝ`. -/
abbrev ExpDecaySchwartzRpos (I : Set ℝ) : Type := ExpDecaySchwartz (Multiplicative ℝ) rposModule I

/-- The Mellin transform `M(ϕ)(s) = ∫_0^∞ ϕ(t) t^s dt/t = ∫_ℝ ϕ(e^x) e^{sx} dx` of
`ϕ ∈ S_I(ℝ_{>0})`. -/
def ExpDecaySchwartzRpos.mellin {I : Set ℝ} (ϕ : ExpDecaySchwartzRpos I) (s : ℂ) : ℂ :=
  ∫ x : ℝ, ϕ.toFun (Multiplicative.ofAdd x) * Complex.exp (s * x)

end

end MasulloGRH


