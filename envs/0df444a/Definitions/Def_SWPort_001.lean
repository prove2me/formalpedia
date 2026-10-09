-- Prove2me | Definitions.Def_SWPort_001
-- name    : SWPort_001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T19:20:41.553327+00:00
-- url     : https://prove2.me/theorems/62b32f72-8d37-4281-a8bc-d937e7bd5c97
-- title:
--   Siegel–Walfisz port, definitions bundle 2 of 2 — Davenport's ψ(N; q, a), zero-free regions and exceptional zeros
-- statement:
--   The second of two definitions bundles of a port of prove2.me user alya's proof of the Siegel–Walfisz theorem (`Davenport.siegel_walfisz_ap`, ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003) to the Mathlib 0df444a environment. It imports `SWPort_000`.
--
--   It collects, under the namespace `SWPort`, the definitions of alya's Davenport development (following Davenport, *Multiplicative Number Theory*). These include $\psi(N;q,a)$, the zero-free region `InRegion`, exceptional sets of zeros `IsExceptionalSet`, the shared objects of the `Vino` and `Davenport` bundles, and the auxiliary objects of the bridge to the $\pi$/Li form used by OpenAI's *Primitive roots for every admissible integer base* (2026). The bundle also holds the lemmas those definitions use in their bodies.
--
--   Each module section names, in a comment, the original prove2.me bundle it was ported from, with that bundle's id. The definitions are unchanged apart from compatibility edits for the newer Mathlib and the `SWPort` namespace.
-- source:
--   prove2.me user alya's proof of the Siegel–Walfisz theorem, Davenport.siegel_walfisz_ap (ff9f3207-eba1-492e-9691-e50480292b68, Mathlib c5ea003), following H. Davenport, Multiplicative Number Theory; ported to Mathlib 0df444a; Davenport and Vino bundles by alya

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_ArtinSieve
import Definitions.Def_SWPort_000

section
-- module Solutions.Artin.SW.BridgeCore
/-!
# From the `ψ` form of Siegel–Walfisz to the `π`/`Li` form

`SWPsi` is the progression form `ψ(N;q,a) = N/φ(q) + O(N exp(-c √log N))` for `q ≤ (log N)^A`,
with `ψ(N;q,a) = ∑_{n<N, n ≡ a (q)} Λ(n)` written out exactly as alya's `Davenport.psiAP`
(prove2.me theorem `Davenport.siegel_walfisz_ap`, ff9f3207).  `siegel_walfisz_of_psi` derives
`ArtinPrimitiveRoots.siegel_walfisz` from it by partial summation: prime powers cost
`O(√k log k)`, moduli below `√Y` are bounded trivially, and `exp(-c √log Y)` beats every power of
`log Y`.

The partial-summation lemmas (`abel_sum_real` … `abs_thetaq_sub_psiAP_le`) are copied from our
Bombieri–Vinogradov development `Solutions/Artin/BV` (LiSum, Transfer1, Transfer2).
-/

namespace SWPort.Bridge

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-! ## Partial summation (from `Solutions/Artin/BV`) -/

/-- `θ(k; q, a)`. -/
noncomputable def thetaq (k q a : ℕ) : ℝ :=
  ∑ j ∈ Ioc 1 k, (if j.Prime ∧ j ≡ a [MOD q] then Real.log j else 0)

/-- The error `G_q(k) = θ(k; q, a) - (k - 1)/φ(q)`. -/
noncomputable def Gq (k q a : ℕ) : ℝ :=
  ∑ j ∈ Ioc 1 k, ((if j.Prime ∧ j ≡ a [MOD q] then Real.log j else 0) - 1 / q.totient)

/-- `ψ(k; q, a) = ∑_{n ≤ k, n ≡ a (q)} Λ(n)`. -/
noncomputable def psiAP (k q a : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 k).filter (fun n => n ≡ a [MOD q]), Λ n

/-! ## New: the bridge -/

/-- The `ψ` form of Siegel–Walfisz, with `ψ(N;q,a) = ∑_{n<N, n ≡ a (q)} Λ(n)` spelled out as in
`Davenport.psiAP`; this is the statement of `Davenport.siegel_walfisz_ap` (alya, prove2.me
ff9f3207). -/
def SWPsi : Prop :=
  ∀ A : ℝ, 0 < A → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (N q a : ℕ), 2 ≤ N → 1 ≤ q → (q : ℝ) ≤ Real.log N ^ A → Nat.Coprime a q →
      |(∑ n ∈ range N,
          if (n : ZMod q) = (a : ZMod q) then (ArithmeticFunction.vonMangoldt n : ℝ) else 0)
          - (N : ℝ) / (Nat.totient q : ℝ)|
        ≤ C * N * Real.exp (-c * Real.sqrt (Real.log N))

end SWPort.Bridge
end

section
-- module Solutions.Artin.SW.Def.Vino_dirichlet
namespace SWPort
/-! Ported from prove2.me definition bundle `Vino_dirichlet` (c1d62205-17c4-4452-bb67-988fb2a1dba7, by tabbott). -/



namespace Vino

/-- The von Mangoldt sum twisted by a Dirichlet character,
`ψ(N, χ) = ∑_{n < N} Λ(n) χ(n)`. -/
noncomputable def vmSumChar (q : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)

end Vino

end SWPort
end

section
-- module Solutions.Artin.SW.Def.Davenport_siegelWalfisz
namespace SWPort
/-! Ported from prove2.me definition bundle `Davenport_siegelWalfisz` (9ed9bea4-6855-4ea9-bdbe-3e06e0b53526, by alya). -/
/-
# Siegel–Walfisz: vocabulary (Davenport, *Multiplicative Number Theory*, 3rd ed., §§14, 18–22)

This file fixes the objects used to state the Siegel–Walfisz theorem and the results of
Davenport §§14, 18, 20, 21 that lead to it.  The character-twisted sum
`ψ(N, χ) = ∑_{n < N} Λ(n) χ(n)` is `Vino.vmSumChar q χ N` (platform definition
`Vino_dirichlet`), and `L(s, χ)` is Mathlib's `DirichletCharacter.LFunction`.

Convention: sums are over `n < N` with `N : ℕ` (as in `Vino.vmSumChar` and
`ThreePrimes.SiegelWalfisz`); Davenport sums over `n ≤ x`.  The two differ by the single
term `Λ(N) ≤ log N`, which is negligible against every error term below.
-/







open Finset

namespace Davenport

/-- `ψ(N; q, a) = ∑_{n < N, n ≡ a (mod q)} Λ(n)`, the von Mangoldt sum over an arithmetic
progression (Davenport §20, first sentence, with `n ≤ x` replaced by `n < N`). -/
noncomputable def psiAP (N q a : ℕ) : ℝ :=
  ∑ n ∈ range N,
    if (n : ZMod q) = (a : ZMod q) then (ArithmeticFunction.vonMangoldt n : ℝ) else 0

/-- The boundary `1 - c / log (q (|t| + 2))` of the classical zero-free region for
`L(s, χ)`, `χ` a character modulo `q`, at height `t = Im s` (Davenport §14). -/
noncomputable def regionBoundary (c : ℝ) (q : ℕ) (s : ℂ) : ℝ :=
  1 - c / Real.log ((q : ℝ) * (|s.im| + 2))

/-- `s` lies in the closed region `Re s ≥ 1 - c / log (q (|Im s| + 2))`. -/
def InRegion (c : ℝ) (q : ℕ) (s : ℂ) : Prop := regionBoundary c q s ≤ s.re

/-- `E` is an *exceptional set* for `χ` (modulo `q`) with respect to the region constant `c`:
`E` has at most one element; every element of `E` is a real zero of `L(·, χ)` in `(0, 1)` lying
in the region, and such an element can exist only when `χ` is a real (quadratic) non-principal
character;
and `L(s, χ) ≠ 0` at every `s ≠ 1` of the region `Re s ≥ 1 - c / log (q (|Im s| + 2))`
outside `E`.  (Davenport §14: "at most one exceptional real zero".) -/
def IsExceptionalSet {q : ℕ} [NeZero q] (c : ℝ) (χ : DirichletCharacter ℂ q) (E : Set ℂ) :
    Prop :=
  E.Subsingleton ∧
    (∀ z ∈ E, z.im = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ InRegion c q z ∧
      DirichletCharacter.LFunction χ z = 0 ∧ χ.IsQuadratic ∧ χ ≠ 1) ∧
    ∀ s : ℂ, s ≠ 1 → InRegion c q s → s ∉ E → DirichletCharacter.LFunction χ s ≠ 0

end Davenport

end SWPort
end

section
-- module Solutions.Artin.SW.Def.EulerMaclaurin_defs
namespace SWPort
/-! Ported from prove2.me definition bundle `EulerMaclaurin_defs` (31dad85f-f1fe-4761-8761-fd383156de21, by Community (Bot)). -/


/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

section

open Finset Interval MeasureTheory


variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2
end

end SWPort
end

section
-- module Solutions.Artin.SW.Def.Rectangle_defs
namespace SWPort
/-! Ported from prove2.me definition bundle `Rectangle_defs` (0a8a3c2f-e233-4739-9f57-3945a05c3db8, by Community (Bot)). -/




open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

/-- A `RectangleBorder` has corners `z` and `w`. -/
def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]

end SWPort
end

section
-- module Solutions.Artin.SW.Def.ResidueCalcOnRectangles_defs
namespace SWPort
/-! Ported from prove2.me definition bundle `ResidueCalcOnRectangles_defs` (f82527a4-e4e4-4999-9ab9-d940d8b0546f, by Community (Bot)). -/











open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)

noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)


/-- A `RectangleIntegral` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`. -/
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im

/-- A `RectangleIntegral'` of a function `f` is one over a rectangle
  determined by `z` and `w` in `ℂ`, divided by `2 * π * I`. -/
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w


/-- A function is `HolomorphicOn` a set if it is complex
  differentiable on that set. -/
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s


def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im


/-! ## Residue calculus: residues, simple poles, and the rectangle residue theorem

The simple-pole `residue`, `sumResiduesIn`, the `HasSimplePolesOn` scaffold, and the rectangle
residue theorem `RectangleIntegral'_eq_sumResiduesIn`. Extracted from `CH2.lean` as general,
reusable contour-integration lemmas (see issue #1537). -/


-- If two functions `f g : ℂ → ℂ` agree on a `codiscreteWithin R` full set, and `φ : ℝ → ℂ` is
-- an analytic non-constant path mapping `[a,b]` into `R`, then `∫ f(φ x) dx = ∫ g(φ x) dx`.
-- (a.e. agreement along the preimage suffices for interval integrals)

-- Under `HasSimplePolesOn f U`, every point with strictly negative meromorphic order has order
-- exactly -1: the simple-pole hypothesis gives `(-1 : ℤ) ≤ order`, negativity gives `order < 0`,
-- so the only integer fitting both is -1.

-- At a simple pole `p` of `f` inside `U`, the residue of the meromorphic normal form
-- `toMeromorphicNFOn f U` equals the residue of `f`. The two functions agree on a punctured
-- neighborhood of `p` (by definition of the normal form), so their `(z - p) * ·` limits coincide.

-- Non-constancy of horizontal paths `x ↦ x + h * I`.

-- Non-constancy of vertical paths `y ↦ r + y * I`.

-- Helper for horizontal integral congruence on codiscrete set

-- Helper for vertical integral congruence on codiscrete set

-- At the boundary, `f` and its normal-form representative differ only at a discrete set
-- of poles, so their boundary integrals coincide.


-- Since no poles lie on the boundary of the rectangle, the principal part is continuous
-- on the boundary and therefore integrable.


-- The integral of a sum of simple pole terms `c p / (s - p)` along the boundary of the rectangle
-- equals the sum of the coefficients `c p` for all points `p` in the interior.

-- Splits the integral of `fNF` into the integral of its holomorphic part and its principal part.

end SWPort
end

section
-- module Solutions.Artin.SW.Def.Vino_threeprimes
namespace SWPort
/-! Ported from prove2.me definition bundle `Vino_threeprimes` (f0c405a4-66a9-4864-8b3d-0917ce24ebe6, by tabbott). -/
/-
# Vinogradov's three primes theorem, conditional on Siegel–Walfisz — statement and reduction

## What this file is

The three primes theorem (every sufficiently large odd `n` is a sum of three primes) is
proved by the Hardy–Littlewood–Vinogradov circle method.  Its major-arc analysis needs the
prime number theorem in arithmetic progressions with an error term uniform in the modulus
`q ≤ (log N)^A` — the **Siegel–Walfisz theorem** — which Mathlib does not have.  This file

1. states Siegel–Walfisz as a `Prop` (`SiegelWalfisz`), in the *Dirichlet character* form;
2. states the weighted asymptotic `R(n) = ½ 𝔖(n) n² + o(n²)` and the existence theorem,
   both conditional on `SiegelWalfisz`;
3. reduces them to explicitly stated pieces, each proved here or AVAILABLE on the platform
   (the file is now complete: every piece is discharged);
4. proves the assembly bookkeeping, the passage from the asymptotic to the existence
   statement, the major-arc main-term identity, and the elementary estimates.

The structural template is `Solutions/M_waring_final.lean` (the proved Waring assembly).

## Why the character form of Siegel–Walfisz

`Vino.vmSum_coprime_char_expansion` (platform, Proved) writes the coprime part of the
exponential sum at a rational point as

  `φ(q) ∑_{n<N, (n,q)=1} Λ(n) e(bn/q) = ∑_{χ mod q} χ⁻¹(b) τ(χ) ψ(N, χ⁻¹)`,

so the input the major arcs actually consume is a bound on `ψ(N,χ) = ∑_{n<N} Λ(n)χ(n)` for
*every* character `χ` mod `q`, uniformly in `q ≤ (log N)^A`.  This is also the form in which
Siegel–Walfisz is proved (zero-free regions of `L(s,χ)` plus Siegel's theorem); the
arithmetic-progression form `ψ(N;q,a) = N/φ(q) + O(N e^{-c√log N})` is *derived* from it by
finite character orthogonality, and conversely, so nothing is lost.  Finally, the character
form makes the principal-character case explicit: `χ = 1` is the prime number theorem with
the de la Vallée-Poussin error term, up to the `O(log q · log N)` contribution of the
`n` sharing a factor with `q`.

## Parameters

`N = n + 1` (so `∑_{a,b,c<N}` captures every representation of `n`);
`P = ⌊(log n)^B⌋₊ + 1` with `B > 12` fixed (the major arcs are `|α − a/q| ≤ P/N`, `q ≤ P`);
Farey order `Q = ⌊N/P⌋` for the dissection.  On the minor arcs `q > P`, and the Vaughan bound
gives `‖S‖ ≪ N (log N)^{4 − B/2}`; with Parseval `∫|S|² ≤ N (log N)²` the minor-arc integral is
`≪ N² (log N)^{6 − B/2} = o(N²)`.  On the major arcs Siegel–Walfisz with `A = B` gives
`S(a/q+β) = μ(q)/φ(q)·v(β) + O(q (1+|β|N) N (log N)^{-B'})`, and the total major-arc error is
`≪ N² P⁵ (log N)^{2−B'} = o(N²)` for `B' > 5B + 2`.
-/













































































open Vino Finset Filter Asymptotics MeasureTheory
open scoped Topology

namespace ThreePrimes

open Classical in
/-- **Siegel–Walfisz** (character form).  For every `A > 0` there are constants `C` and
`c > 0` such that for every modulus `q ≥ 1`, every Dirichlet character `χ` mod `q`, and every
`N ≥ 2` with `q ≤ (log N)^A`,

  `‖ψ(N, χ) − δ_χ N‖ ≤ C N exp(−c √(log N))`,

where `ψ(N,χ) = ∑_{n<N} Λ(n) χ(n)` (`Vino.vmSumChar`) and `δ_χ = 1` for the principal
character and `0` otherwise.  (The `χ = 1` case is the prime number theorem with the de la
Vallée-Poussin error term, up to the `O(log q · log N)` mass of the `n` not coprime to `q`.) -/
def SiegelWalfisz : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C c : ℝ, 0 < c ∧
    ∀ (q : ℕ), 1 ≤ q → ∀ (χ : DirichletCharacter ℂ q) (N : ℕ), 2 ≤ N →
      (q : ℝ) ≤ Real.log N ^ A →
        ‖vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)‖
          ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

end ThreePrimes

end SWPort
end

section
-- module Solutions.Artin.SW.Def.ZetaBounds_defs
namespace SWPort
/-! Ported from prove2.me definition bundle `ZetaBounds_defs` (31032376-68b0-4d6c-8bf5-1aacf266a5c3, by Community (Bot)). -/
































set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics


local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta


-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/


-- Alternative cleaner proof using more direct approach


/- The set should be open so that f'(p) = O(1) for all p ∈ U -/


noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0


-- move near `Real.differentiableAt_rpow_const_of_ne`


noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))


-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`


-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**


-- **End collaboration 6/20/25**


/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/


-- **Begin collaboration with the Alpha Proof team! 5/29/25**


-- **End collaboration**


open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_deriv_LFunction_bound
namespace SWPort
/-! Ported from prove2.me: `Davenport.deriv_LFunction_bound` (4593099f-60e7-4438-b99c-61d859e045c6, statement by alya); proof = accepted direct submission e970c8ab-fee0-47c1-9a42-03c5c9556b34 by alya. -/












open Finset MeasureTheory Set Complex Filter Topology Asymptotics

namespace DLFB

/-! ### Partial sums of a Dirichlet character -/

variable {q : ℕ} [NeZero q]

/-- The partial character sum `S(t) = ∑_{1 ≤ k ≤ ⌊t⌋} χ(k)`. -/
noncomputable def G_p0 (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k

/-! ### The Mellin representation -/

/-- The Abel-summation integral, an analytic continuation of the L-series to `Re s > 0`. -/
noncomputable def F_p0 (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ := s * mellin (G_p0 χ) (-s)

/-! ### Analytic continuation via the identity theorem -/

/-! ### Elementary real estimates -/

/-! ### Bounding the two Mellin integrals -/

/-! ### A numerical lower bound for `log 3` -/

end DLFB

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.sum_eq_integral_add_integral_deriv
namespace SWPort
/-! Ported from prove2.me: `sum_eq_integral_add_integral_deriv` (bfc44a54-cecc-430a-851f-f34ef8e4e09d, statement by Community (Bot)); proof = accepted direct submission 853bde6f-9f2c-4040-b705-6134375e9070 by Community (Bot). -/



/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

open Finset Interval MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

@[fun_prop]
theorem aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_RvM_norm_riemannZeta_le_of_re_pos
namespace SWPort.Z
/-! Ported from prove2.me: `Zeta23.RvM.norm_riemannZeta_le_of_re_pos` (8c51ba72-b36c-42d5-9d8f-285bed56a247, statement by Community (Bot)); proof = accepted sketch submission 243830a6-8e2f-4acd-ac30-7820552c352c by Community (Bot). -/






































-- from Zeta23.RvM.ZetaGrowth
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ZetaGrowth.lean — growth of ζ in vertical strips (consumed by the Landau/Jensen
local zero count and the Backlund S(T) bound).

CONTENT:
* `norm_riemannZeta_le_of_re_pos` — the explicit half-plane bound
      ‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s        (0 < Re s, s ≠ 1),
  from the N = 1 case of the summation-by-parts representation
      ζ(s) = Σ_{n≤N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx
  [Tit86, (2.1.4) / §2.1], which is `riemannZeta0` / `Zeta23_Zeta0EqZeta` in the PrimeNumberTheoremAnd
  port Zeta23/FromPNTPlus/ZetaBounds.lean (Apache-2.0, see README § Provenance).
* `riemannZeta_linear_growth` — for every δ > 0:  ‖ζ(σ+it)‖ ≤ (5/2 + δ⁻¹)·|t|  (σ ≥ δ, |t| ≥ 1)
  [Tit86, §5.1: ζ(s) = O(|t|) uniformly in σ ≥ δ], and the ∃-constant corollaries
  (`zeta_growth`, `zeta_growth_quarter`).
* `norm_riemannZeta_sub_one_le` — ‖ζ(s) − 1‖ ≤ π²/6 − 1 for Re s ≥ 2, hence the two-sided bounds
  0 < 2 − π²/6 ≤ ‖ζ(s)‖ ≤ π²/6 there (the Jensen/Landau disc centre 2 + it needs ζ ≠ 0 and a
  lower bound at the centre) [Tit86, §9.2 uses |ζ(2+iT)| ≥ … > 0].
* `analyticOnNhd_riemannZeta` — ζ is analytic on any set avoiding 1 (Mathlib's
  differentiableAt_riemannZeta, repackaged for the Jensen hypotheses).

NOT here: anything for Re s ≤ 0 (that needs the functional equation + Γ-ratio growth, i.e.
Stirling); no consumer in this repository needs it (σ ≥ 1/4 suffices).
-/

open Complex Set MeasureTheory Real

open Complex Set MeasureTheory Real

theorem _root_.SWPort.Z.Zeta23.RvM.norm_riemannZeta_le_of_re_pos {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hσ
  have hint := Zeta23_ZetaBnd_aux1b 1 le_rfl (σ := s.re) (t := s.im) hσ
  rw [re_add_im] at hint
  simp only [Nat.cast_one, Real.one_rpow] at hint
  rw [← Zeta23_Zeta0EqZeta (N := 1) one_pos hσ hs]
  simp only [riemannZeta0, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Complex.zero_cpow hs0, Nat.cast_one, Complex.one_cpow, div_one, div_zero, zero_add]
  set J := ∫ x in Ioi (1 : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  calc ‖(1 : ℂ) + -1 / (1 - s) + -1 / 2 + s * J‖
      = ‖(1 / 2 : ℂ) + -(1 / (1 - s)) + s * J‖ := by ring_nf
    _ ≤ ‖(1 / 2 : ℂ)‖ + ‖-(1 / (1 - s))‖ + ‖s * J‖ := norm_add₃_le
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * ‖J‖ := by
        simp [norm_neg]
    _ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ * (1 / s.re) := by gcongr
    _ = 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by ring

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Thm.Davenport_estermann_lemma
namespace SWPort
/-! Ported from prove2.me: `Davenport.estermann_lemma` (478fdf36-d856-42b6-a465-a4a0d385c671, statement by alya); proof = accepted sketch submission c69ce056-e988-46e0-bf72-1469a42d6e88 by alya. -/












open Finset DirichletCharacter

namespace DavenportAux.Estermann

open Complex Topology Filter
open scoped ComplexOrder

/-! ### The entire completion of `ζ s - 1/(s-1)` -/

/-- `ζ s - 1/(s-1)`, made entire by giving it the value `γ` at `s = 1`. -/
noncomputable def zeta0 : ℂ → ℂ :=
  Function.update (fun s => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

/-! ### The auxiliary function `G` -/

/-! ### Numerical lemmas -/

end DavenportAux.Estermann

open DavenportAux.Estermann
open Topology
open scoped ComplexOrder

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.ZerosBound
namespace SWPort.Z
/-! Ported from prove2.me: `ZerosBound` (c3517640-7df9-4cb9-aa6a-4f657187895a, statement by Community (Bot)); proof = accepted sketch submission a8bbe574-9eee-4295-90cb-1d8b44620b45 by Community (Bot). -/













-- from Zeta23.FromPNTPlus.StrongPNTPrefix
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/StrongPNT.lean (sorry-free prefix, truncated before JBlaschke/ZeroInequality).
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: kept only a prefix of the file (through `ZerosBound`: the Blaschke-factor /
Borel–Carathéodory bound on zeros in a disk; the remainder of StrongPNT.lean is not ported),
removed the Architect blueprint tooling (import Architect, blueprint_comment blocks,
@[blueprint ...] attributes), dropped the intra-project import of MediumPNT together with the
local notations and the `open ArithmeticFunction` that only the unported remainder used (the two Mathlib
imports previously reached through MediumPNT are imported directly), and added
`import Zeta23.Prelude.InstancePriorities` (this project's instance-priority settings).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory










open Classical






lemma BlaschkeAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (BlaschkeB r R f) (Metric.closedBall (0 : ℂ) R) := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  unfold BlaschkeB
  by_cases finite_zeros_mono : (SetOfZeros r f).Finite
  · simp only [finite_zeros_mono, ↓reduceDIte]
    refine AnalyticOnNhd.mul (CfAnalytic r_lt_R R_lt_one hfAnalytic hf_neq_zero_at_zero) (Finset.analyticOnNhd_fun_prod (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset ?_)
    intro w hw
    refine AnalyticOnNhd.fun_pow (AnalyticOnNhd.sub (analyticOnNhd_const) (AnalyticOnNhd.div (AnalyticOnNhd.mul (analyticOnNhd_id) (analyticOnNhd_const)) (analyticOnNhd_const) ?_)) (analyticOrderAt f w).toNat
    intro w' hw'
    exact_mod_cast ne_of_gt R_pos
  · simp only [finite_zeros_mono, ↓reduceDIte]
    exact analyticOnNhd_const

lemma BlaschkeOfZero {r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    ‖BlaschkeB r R f 0‖ =
      ‖f 0‖ * (∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ (analyticOrderNatAt f ρ)) := by
  have zero_not_zero : ¬(0 ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    simp only [norm_zero, not_and]
    intro r
    exact mem_support.mp hf_neq_zero_at_zero
  unfold BlaschkeB Cf
  simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, zero_not_zero, ↓reduceDIte, zero_sub, zero_mul, zero_div, sub_zero,
    Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow, norm_neg, norm_real, norm_eq_abs]
  rw[div_eq_mul_inv, mul_assoc, abs_of_pos (by linarith)]
  refine (mul_right_inj' (norm_ne_zero_iff.mpr hf_neq_zero_at_zero)).mpr ?_
  rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  simp only [div_eq_inv_mul, mul_pow, inv_pow]


lemma DiskBound {B r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_pos : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    (finiteZeros : (SetOfZeros 1 f).Finite)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) (fz_bound : ∀ (z : ℂ), ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    ‖BlaschkeB r R f z‖ ≤ B := by
  have r_lt_one : r < 1 := lt_trans r_lt_R R_lt_one
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  refine AnalyticOn.norm_le_of_norm_le_on_sphere (Std.IsPreorder.le_refl R) (AnalyticOnNhd.analyticOn (BlaschkeAnalytic r_pos r_lt_R R_lt_one finiteZeros hfAnalytic hf_neq_zero_at_zero)) ?_ hz
  intro w hw
  rw[mem_sphere_iff_norm, sub_zero] at hw
  have hw_not_in : ¬(w ∈ SetOfZeros r f) := by
    apply notMem_setOf_iff.mpr
    intro le_r
    linarith
  have Bf_eq_f_at_w : ‖BlaschkeB r R f w‖ = ‖f w‖ := by
    unfold BlaschkeB Cf
    simp only [finiteSetOfZeros_mono r_lt_one finiteZeros, hw_not_in, ↓reduceDIte, Complex.norm_mul, Complex.norm_div, norm_prod, norm_pow]
    rw[div_eq_mul_inv, mul_assoc, mul_right_eq_self₀]
    by_cases fw_normZero : ‖f w‖ = 0
    · exact Or.inr fw_normZero
    · apply Or.inl
      rw[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro w' hw'_in
      have hfact : (R : ℂ) - w * starRingEnd ℂ w' / R = (conj w - conj w') * w / R := by
        rw[sub_mul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hw, ofReal_pow]
        field_simp
      rw [hfact, norm_div, norm_mul, ← map_sub, norm_conj, Complex.norm_real, hw, Real.norm_of_nonneg (le_of_lt R_pos)]
      field_simp
      rw[← div_pow, div_self, one_pow]
      rw[Set.Finite.mem_toFinset] at hw'_in
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => hw_not_in (h ▸ hw'_in)))
  rw[Bf_eq_f_at_w]
  exact fz_bound w (le_of_eq hw)



open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
open Classical

theorem _root_.SWPort.Z.ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by
  have R_pos : 0 < R := lt_trans r_pos r_lt_R
  have hf0_ne_zero : f 0 ≠ 0 := by rw [hf0_eq_one]; exact one_ne_zero
  have blaschke_eq := BlaschkeOfZero r_pos r_lt_one r_lt_R finiteZeros hf0_ne_zero
  rw[hf0_eq_one, norm_one, one_mul] at blaschke_eq
  rw [one_div, inv_mul_eq_div, le_div_iff₀ (Real.log_pos (by simp only [lt_div_iff₀ r_pos, one_mul, r_lt_R])), ← Real.log_pow]
  refine Real.log_le_log (pow_pos (div_pos R_pos r_pos) _) ?_
  calc (R / r) ^ ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ
      = ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / r) ^ analyticOrderNatAt f ρ := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, (R / ‖ρ‖) ^ analyticOrderNatAt f ρ := by
      apply Finset.prod_le_prod
      · intro ρ _
        exact pow_nonneg (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) _
      · intro ρ hρ
        have hρ_mem := (finiteSetOfZeros_mono r_lt_one finiteZeros).mem_toFinset.mp hρ
        refine pow_le_pow_left₀ (div_nonneg (le_of_lt R_pos) (le_of_lt r_pos)) ?_ _
        refine div_le_div_of_nonneg_left (le_of_lt R_pos) (norm_pos_iff.mpr ?_) (hρ_mem.1)
        rintro rfl
        exact hf0_ne_zero hρ_mem.2
    _ ≤ B := by
      rw[← blaschke_eq]
      exact DiskBound r_pos r_lt_R R_lt_one finiteZeros hfAnalytic
        hf0_ne_zero fz_bound (Metric.mem_closedBall_self (le_of_lt R_pos))

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_WeilEF_logDeriv_split
namespace SWPort.Z
/-! Ported from prove2.me: `Zeta23.WeilEF.logDeriv_split` (b8a6d5d9-c28a-41f4-91d3-148b1e0513db, statement by Community (Bot)); proof = accepted sketch submission ca01e91f-4038-47ae-8b09-1018556c1fcc by Community (Bot). -/































































-- from Zeta23.WeilEF.Landau
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Landau.lean

Landau's lemma (Borel–Carathéodory + Jensen route; Mathlib: Analysis/Complex/BorelCaratheodory,
JensenFormula): zero counts and the partial-fraction expansion of f'/f on disks, specialized to ζ.
`zeta_local_zero_count` is consumed downstream as `RiemannVonMangoldt.local_count`.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set


section UnitDisk

open Metric


/-- Away from the zero set, `f = Π (z−ρ)^{m_ρ} · Cf`. -/
lemma f_eq_prod_mul_Cf {f : ℂ → ℂ} {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : z ∉ SetOfZeros r f) :
    f z = (∏ ρ ∈ (finiteSetOfZeros_mono hr1 hfin).toFinset, (z - ρ) ^ analyticOrderNatAt f ρ)
      * Cf r f z := by
  have hfinr := finiteSetOfZeros_mono hr1 hfin
  unfold Cf
  rw [dif_pos hfinr, dif_neg hz]
  rw [mul_div_cancel₀]
  refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
  have hρ' := hfinr.mem_toFinset.mp hρ
  have hne : z ≠ ρ := by
    rintro rfl
    exact hz hρ'
  exact pow_ne_zero _ (sub_ne_zero.mpr hne)

/-- logDeriv of the finite zero product: `logDeriv (Π (·−ρ)^{m_ρ}) z = Σ m_ρ/(z−ρ)`
(Mathlib's `logDeriv_prod` + `logDeriv_fun_pow`). -/
lemma logDeriv_zero_prod {s : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : ∀ ρ ∈ s, z ≠ ρ) :
    logDeriv (fun w => ∏ ρ ∈ s, (w - ρ) ^ m ρ) z = ∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ))) (fun ρ _ => by fun_prop)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hd : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  rw [logDeriv_fun_pow hd.differentiableAt, logDeriv_apply, hd.deriv]
  ring







end UnitDisk



end WeilEF
end Zeta23
end
open SWPort.Z.Zeta23
open SWPort.Z.Zeta23.WeilEF
open Complex Set
open Metric

theorem _root_.SWPort.Z.Zeta23.WeilEF.logDeriv_split {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ < r) (hfz : f z ≠ 0) :
    logDeriv f z = (∑ ρ ∈ (finiteSetOfZeros_mono hr1 hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) + logDeriv (Cf r f) z := by
  have hfinr := finiteSetOfZeros_mono hr1 hfin
  set P0 : ℂ → ℂ := fun w => ∏ ρ ∈ hfinr.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ with hP0
  have hU : IsOpen (Metric.ball (0 : ℂ) r \ SetOfZeros r f) :=
    Metric.isOpen_ball.sdiff hfinr.isClosed
  have hzU : z ∈ Metric.ball (0 : ℂ) r \ SetOfZeros r f :=
    ⟨mem_ball_zero_iff.mpr hz, fun h => hfz h.2⟩
  have heq : f =ᶠ[nhds z] fun w => P0 w * Cf r f w := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact f_eq_prod_mul_Cf hr1 hfin hw.2
  have hzne : ∀ ρ ∈ hfinr.toFinset, z ≠ ρ := by
    intro ρ hρ
    rintro rfl
    exact hfz (hfinr.mem_toFinset.mp hρ).2
  have hP0z : P0 z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hzne ρ hρ))
  have hCfz : Cf r f z ≠ 0 := Cf_ne_zero hfa hf0 hr1 hfin hz.le
  have hdP0 : DifferentiableAt ℂ P0 z :=
    DifferentiableAt.fun_finsetProd fun ρ _ =>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
  have hdCf : DifferentiableAt ℂ (Cf r f) z := by
    have hR : r < (r + 1) / 2 := by linarith
    have hR1 : (r + 1) / 2 < 1 := by linarith
    exact ((CfAnalytic hR hR1 hfa hf0) z (by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
      calc ‖z‖ ≤ r := hz.le
        _ ≤ (r + 1) / 2 := by linarith)).differentiableAt
  calc logDeriv f z = logDeriv (fun w => P0 w * Cf r f w) z := by
        unfold logDeriv
        simp only [Pi.div_apply]
        rw [heq.deriv_eq, heq.eq_of_nhds]
    _ = logDeriv P0 z + logDeriv (Cf r f) z := logDeriv_mul z hP0z hCfz hdP0 hdCf
    _ = _ := by rw [hP0, logDeriv_zero_prod hzne]

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_WeilEF_norm_logDeriv_Cf_le
namespace SWPort.Z
/-! Ported from prove2.me: `Zeta23.WeilEF.norm_logDeriv_Cf_le` (143eab74-b138-450b-b3a0-9ad14c01ab6d, statement by Community (Bot)); proof = accepted sketch submission d089ab27-fb26-4b8b-ac51-8480154a4391 by Community (Bot). -/


































































-- from Zeta23.FromPNTPlus.StrongPNTPrefix
section
/-
Ported from https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
at commit 6a380f0c4658c04a420a9eb00b1ed62a1e3fde01 (tag v4.32.2), file
PrimeNumberTheoremAnd/StrongPNT.lean (sorry-free prefix, truncated before JBlaschke/ZeroInequality).
Copyright the PrimeNumberTheoremAnd contributors; Apache License 2.0
(http://www.apache.org/licenses/LICENSE-2.0).
Local modifications: kept only a prefix of the file (through `ZerosBound`: the Blaschke-factor /
Borel–Carathéodory bound on zeros in a disk; the remainder of StrongPNT.lean is not ported),
removed the Architect blueprint tooling (import Architect, blueprint_comment blocks,
@[blueprint ...] attributes), dropped the intra-project import of MediumPNT together with the
local notations and the `open ArithmeticFunction` that only the unported remainder used (the two Mathlib
imports previously reached through MediumPNT are imported directly), and added
`import Zeta23.Prelude.InstancePriorities` (this project's instance-priority settings).
Re-ported from the
v4.29.0 port (commit 10e1218932db7e2432aa5881d750acb819e91f19) when the project
moved to Lean v4.32.2 / Mathlib 905b95818eb32af7874a58b427f50c1711a5e96c.
Modified 2026 by Anthropic PBC.
-/

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory


theorem borelCaratheodory' {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (Rpos : 0 < R) (hyp_r : r < R)
    (analytic : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have h_borelCaratheodory : ∀ ε > 0, ‖f z‖ ≤ (2 * (M + ε) * ‖z‖) / (R - ‖z‖) := by
    intro ε εpos;
    apply Complex.borelCaratheodory_zero;
    exacts [by linarith, analytic.differentiableOn, fun z hz => by rw [Set.mem_setOf_eq]; linarith [realPartBounded z hz], Rpos, by exact Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp hyp_z ) hyp_r ), zeroAtZero]
  have h_limit : ‖f z‖ ≤ (2 * M * ‖z‖) / (R - ‖z‖) := by
    have h_limit : Filter.Tendsto (fun ε => (2 * (M + ε) * ‖z‖) / (R - ‖z‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * M * ‖z‖) / (R - ‖z‖))) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' ?_ _ _ (by ring_nf))
      exact ((continuous_const.mul (continuous_const.add continuous_id)).mul continuous_const).div_const _
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_borelCaratheodory ε hε );
  rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
  refine le_trans h_limit ?_;
  gcongr
  · exact mul_nonneg (mul_nonneg (zero_le_two) (le_of_lt Mpos)) (le_trans (norm_nonneg z) hyp_z)

lemma cauchy_formula_deriv {r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]

lemma DerivativeBound {M r r' R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (pos_r : 0 < r) (r_lt_r' : r < r') (r'_lt_R : r' < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (z_in_r : z ∈ Metric.closedBall 0 r) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [cauchy_formula_deriv r_lt_r' r'_lt_R analytic_f.differentiableOn  z_in_r, one_div]
  grw [circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by linarith) (C := 2 * M * r' / ((R - r') * (r' - r) ^ 2))]
  · exact le_of_eq (by ring)
  · intro z' hz'
    rw [smul_eq_mul, norm_mul]
    grw[borelCaratheodory' Mpos (by grind) r'_lt_R analytic_f f_zero_at_zero  re_f_le_M
      (Metric.sphere_subset_closedBall hz')]
    suffices ‖(z' - z)⁻¹ ^ 2‖ ≤ 1 / (r' - r) ^ 2 by
      grw [this]
      · exact le_of_eq (by field)
      · refine mul_nonneg (mul_nonneg ?_ ?_) (inv_nonneg.mpr ?_) <;> linarith
    have hdist : r' - r ≤ ‖z' - z‖ := by
      simp only [mem_sphere_iff_norm, sub_zero, Metric.mem_closedBall,
        _root_.dist_zero_right] at hz' z_in_r
      rw [← hz']
      exact le_trans (by linarith) (norm_sub_norm_le z' z)
    rw [norm_pow, norm_inv, one_div, inv_pow]
    gcongr

theorem BorelCaratheodoryDeriv {M r R : ℝ} {f : ℂ → ℂ} {z : ℂ}
    (Mpos : 0 < M) (rpos : 0 < r) (hyp_r : r < R)
    (analytic_f : AnalyticOn ℂ f (Metric.ball 0 R))
    (zeroAtZero : f 0 = 0)
    (realPartBounded : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
  have hr' : 2 * M * ((R + r) / 2) ^ 2 / ((R - (R + r) / 2) * ((R + r) / 2 - r) ^ 2) =
      4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by field_simp; ring
  calc ‖deriv f z‖
      _ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := hr' ▸
          DerivativeBound Mpos rpos (by linarith) (by linarith) analytic_f zeroAtZero realPartBounded hyp_z
      _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
          have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
          rw [this]; bound





open Classical












end

-- from Zeta23.WeilEF.Landau
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Landau.lean

Landau's lemma (Borel–Carathéodory + Jensen route; Mathlib: Analysis/Complex/BorelCaratheodory,
JensenFormula): zero counts and the partial-fraction expansion of f'/f on disks, specialized to ζ.
`zeta_local_zero_count` is consumed downstream as `RiemannVonMangoldt.local_count`.
-/

open SWPort.Z.Zeta23
open SWPort.Z.Zeta23.WeilEF
open Complex Set
open Metric

theorem _root_.SWPort.Z.Zeta23.WeilEF.norm_logDeriv_Cf_le {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (SetOfZeros 1 f).Finite) (hB2 : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) :
    ‖logDeriv (Cf (22/25) f) z‖ ≤ 44795000 * Real.log B := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hfinr : (SetOfZeros (22/25) f).Finite := finiteSetOfZeros_mono (by norm_num) hfin
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  -- total multiplicity bound (ZerosBound with r = 22/25, R = 24/25)
  have hcount : ((∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset,
      analyticOrderNatAt f ρ : ℕ) : ℝ) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B := by
    exact_mod_cast ZerosBound (by norm_num) (by norm_num)
      (by norm_num : (22/25:ℝ) < 24/25) (by norm_num) hfa hf0 hfin (fun w hw => hfB w hw)
  set K : ℕ := ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset,
    analyticOrderNatAt f ρ with hK
  -- Cf on the sphere of radius 24/25
  have hsphere : ∀ w : ℂ, ‖w‖ = 24/25 → ‖Cf (22/25) f w‖ ≤ B * (25/2 : ℝ) ^ K := by
    intro w hw
    have hwmem : w ∉ SetOfZeros (22/25) f := by
      intro h
      have := h.1
      rw [hw] at this
      norm_num at this
    have hfinr34 := finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin
    have hdist : ∀ ρ ∈ hfinr34.toFinset, (2/25 : ℝ) ≤ ‖w - ρ‖ := by
      intro ρ hρ
      have hρ' := hfinr34.mem_toFinset.mp hρ
      calc (2/25 : ℝ) = 24/25 - 22/25 := by norm_num
        _ ≤ ‖w‖ - ‖ρ‖ := by
            have := hρ'.1
            rw [hw]
            linarith
        _ ≤ ‖w - ρ‖ := norm_sub_norm_le w ρ
    have hprod_lb : ((2/25 : ℝ)) ^ K ≤ ‖∏ ρ ∈ hfinr34.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
      rw [norm_prod, hK, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      rw [norm_pow]
      exact pow_le_pow_left₀ (by norm_num) (hdist ρ hρ) _
    unfold Cf
    rw [dif_pos hfinr34, dif_neg hwmem]
    rw [norm_div]
    have hprod_pos : (0:ℝ) < ‖∏ ρ ∈ hfinr34.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ :=
      lt_of_lt_of_le (by positivity) hprod_lb
    rw [div_le_iff₀ hprod_pos]
    calc ‖f w‖ ≤ B := hfB w (le_of_eq hw)
      _ = B * (25/2 : ℝ) ^ K * (2/25 : ℝ) ^ K := by
          rw [mul_assoc, ← mul_pow]
          norm_num
      _ ≤ B * (25/2 : ℝ) ^ K * ‖∏ ρ ∈ hfinr34.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
          have hB0 : (0:ℝ) ≤ B * (25/2 : ℝ) ^ K := by positivity
          exact mul_le_mul_of_nonneg_left hprod_lb hB0
  -- inside by the maximum principle
  have hball : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖Cf (22/25) f w‖ ≤ B * (25/2 : ℝ) ^ K := by
    intro w hw
    have hCfa : AnalyticOn ℂ (Cf (22/25) f) (Metric.closedBall 0 (24/25)) :=
      ((CfAnalytic (by norm_num : (22/25:ℝ) < 39/40) (by norm_num) hfa hf0').mono
        (Metric.closedBall_subset_closedBall (by norm_num))).analyticOn
    refine AnalyticOn.norm_le_of_norm_le_on_sphere le_rfl hCfa (fun v hv => ?_)
      (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero])
    refine hsphere v ?_
    rw [mem_sphere_iff_norm, sub_zero] at hv
    exact hv
  -- lower bound at the centre
  have hCf0 : (1:ℝ) ≤ ‖Cf (22/25) f 0‖ := by
    have h0mem : (0:ℂ) ∉ SetOfZeros (22/25) f := fun h => hf0' h.2
    have hfinr34 := finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin
    unfold Cf
    rw [dif_pos hfinr34, dif_neg h0mem, norm_div, hf0, norm_one]
    rw [le_div_iff₀]
    · rw [one_mul, norm_prod]
      refine Finset.prod_le_one (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      have hρ' := hfinr34.mem_toFinset.mp hρ
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      rw [zero_sub, norm_neg]
      linarith [hρ'.1]
    · rw [norm_prod]
      refine Finset.prod_pos (fun ρ hρ => ?_)
      have hρ' := hfinr34.mem_toFinset.mp hρ
      have hρ0 : ρ ≠ 0 := by
        rintro rfl
        exact hf0' hρ'.2
      rw [norm_pow, zero_sub, norm_neg]
      exact pow_pos (norm_pos_iff.mpr hρ0) _
  -- the analytic logarithm and Borel–Carathéodory
  obtain ⟨J, hJa, hJ0, hJd, hJre⟩ := LogOfAnalyticFunction
    (by norm_num : (0:ℝ) < 17/20) (by norm_num : (17/20:ℝ) < 22/25)
    ((CfAnalytic (by norm_num : (22/25:ℝ) < 9/10) (by norm_num) hfa hf0').mono
      (Metric.closedBall_subset_closedBall (by norm_num)))
    (fun v hv => Cf_ne_zero hfa hf0' (by norm_num) hfin
      (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hv))
  set M' : ℝ := (1 + Real.log (25/2) / Real.log ((24/25) / (22/25))) * Real.log B with hM'
  have hlog76 : (0:ℝ) < Real.log ((24/25) / (22/25)) := Real.log_pos (by norm_num)
  have hM'pos : 0 < M' := by
    rw [hM']
    have : (0:ℝ) < 1 + Real.log (25/2) / Real.log ((24/25) / (22/25)) := by positivity
    positivity
  have hre : ∀ v ∈ Metric.closedBall (0:ℂ) (17/20), (J v).re ≤ M' := by
    intro v hv
    rw [← (hJre v (Metric.closedBall_subset_ball (by norm_num) hv))]
    have hv' : ‖v‖ ≤ 24/25 := by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hv
      linarith
    have h1 : Real.log ‖Cf (22/25) f v‖ ≤ Real.log (B * (25/2 : ℝ) ^ K) := by
      rcases eq_or_ne (Cf (22/25) f v) 0 with h | h
      · rw [h, norm_zero, Real.log_zero]
        refine Real.log_nonneg ?_
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ B * (25/2 : ℝ) ^ K := by
              refine mul_le_mul (by linarith) (one_le_pow₀ (by norm_num)) (by norm_num)
                (by linarith)
      · exact Real.log_le_log (norm_pos_iff.mpr h) (hball v hv')
    have h2 : (0:ℝ) ≤ Real.log ‖Cf (22/25) f 0‖ := Real.log_nonneg hCf0
    have h3 : Real.log (B * (25/2 : ℝ) ^ K) = Real.log B + K * Real.log (25/2) := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    have h4 : (K : ℝ) * Real.log (25/2) ≤ (Real.log B / Real.log ((24/25)/(22/25))) * Real.log (25/2) := by
      have hlog8 : (0:ℝ) ≤ Real.log (25/2) := Real.log_nonneg (by norm_num)
      have hKle : (K:ℝ) ≤ Real.log B / Real.log ((24/25)/(22/25)) := by
        rw [div_eq_inv_mul, ← one_div]
        exact hcount
      exact mul_le_mul_of_nonneg_right hKle hlog8
    have h5 : Real.log ‖Cf (22/25) f v‖ - Real.log ‖Cf (22/25) f 0‖
        ≤ Real.log B + (K:ℝ) * Real.log (25/2) := by
      rw [← h3]
      linarith
    rw [hM']
    calc Real.log ‖Cf (22/25) f v‖ - Real.log ‖Cf (22/25) f 0‖
        ≤ Real.log B + (K:ℝ) * Real.log (25/2) := h5
      _ ≤ Real.log B + (Real.log B / Real.log ((24/25)/(22/25))) * Real.log (25/2) := by linarith
      _ = (1 + Real.log (25/2) / Real.log ((24/25) / (22/25))) * Real.log B := by
          field_simp
  have hbc := BorelCaratheodoryDeriv hM'pos (by norm_num : (0:ℝ) < 83/100)
    (by norm_num : (83/100:ℝ) < 17/20)
    ((hJa.mono (Metric.ball_subset_ball (by norm_num))).analyticOn) hJ0
    (fun v hv => hre v (Metric.ball_subset_closedBall hv))
    (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero])
  have hzmem : z ∈ Metric.closedBall (0:ℂ) (17/20) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    linarith
  have hderivJ : deriv J z = logDeriv (Cf (22/25) f) z := by
    rw [hJd z (by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
      linarith), logDeriv]
    rfl
  rw [← hderivJ]
  refine hbc.trans ?_
  -- 16 * M' * (17/20)^2 / (17/20 - 83/100)^3 = 1445000 * M' ≤ 1445000 * 31 * log B
  have hM'le : M' ≤ 31 * Real.log B := by
    rw [hM']
    have h8 : Real.log (25/2) ≤ 30 * Real.log ((24/25) / (22/25)) := by
      have h714 : (25/2:ℝ) ≤ ((24/25)/(22/25)) ^ (30:ℕ) := by norm_num
      calc Real.log (25/2) ≤ Real.log (((24/25)/(22/25)) ^ (30:ℕ)) :=
            Real.log_le_log (by norm_num) h714
        _ = 30 * Real.log ((24/25)/(22/25)) := by rw [Real.log_pow]; push_cast; ring
    have hcoef : 1 + Real.log (25/2) / Real.log ((24/25) / (22/25)) ≤ 31 := by
      have hd : Real.log (25/2) / Real.log ((24/25)/(22/25)) ≤ 30 :=
        (div_le_iff₀ hlog76).mpr (by linarith)
      linarith
    exact mul_le_mul_of_nonneg_right hcoef hlogB.le
  calc 16 * M' * (17/20:ℝ) ^ 2 / ((17/20:ℝ) - 83/100) ^ 3 = 1445000 * M' := by
        field_simp
        ring
    _ ≤ 1445000 * (31 * Real.log B) := by
        exact mul_le_mul_of_nonneg_left hM'le (by norm_num)
    _ = 44795000 * Real.log B := by ring

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_WeilEF_logDeriv_partial_fraction_disk
namespace SWPort.Z
/-! Ported from prove2.me: `Zeta23.WeilEF.logDeriv_partial_fraction_disk` (536dcf62-842b-4a5b-be8f-1e3bac245a08, statement by Community (Bot)); proof = accepted sketch submission 653054f3-8c2d-42f5-9285-4f1112bc41e4 by Community (Bot). -/

































































-- from Zeta23.WeilEF.Landau
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Landau.lean

Landau's lemma (Borel–Carathéodory + Jensen route; Mathlib: Analysis/Complex/BorelCaratheodory,
JensenFormula): zero counts and the partial-fraction expansion of f'/f on disks, specialized to ζ.
`zeta_local_zero_count` is consumed downstream as `RiemannVonMangoldt.local_count`.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set


section UnitDisk

open Metric






/-- **Landau partial fraction, unit-disk form**: f analytic on the closed unit disk, f(0) = 1,
‖f‖ ≤ B on ‖z‖ ≤ 24/25 (2 ≤ B), finite zero set.  Then for ‖z‖ ≤ 83/100 with f(z) ≠ 0,
logDeriv f z is the sum of m_ρ/(z−ρ) over zeros with ‖ρ‖ ≤ 22/25, up to an error ≤ 44795000 log B. -/
theorem logDeriv_partial_fraction_unit {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (SetOfZeros 1 f).Finite) (hB2 : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25:ℝ) < 1) hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ 44795000 * Real.log B := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hsplit := logDeriv_split hfa hf0' (by norm_num : (22/25:ℝ) < 1) hfin
    (lt_of_le_of_lt hz (by norm_num)) hfz
  rw [hsplit]
  rw [add_sub_cancel_left]
  exact norm_logDeriv_Cf_le hfa hf0 hfin hB2 hfB hz




end UnitDisk



end WeilEF
end Zeta23
end
open SWPort.Z.Zeta23
open SWPort.Z.Zeta23.WeilEF
open Complex Set
open Metric

theorem _root_.SWPort.Z.Zeta23.WeilEF.logDeriv_partial_fraction_disk {f : ℂ → ℂ} {s₀ : ℂ} {R B : ℝ}
    (hR : 0 < R) (hfa : AnalyticOnNhd ℂ f (Metric.closedBall s₀ R)) (hf0 : f s₀ ≠ 0)
    (hB2 : 2 ≤ B) (hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * R), ‖f w‖ ≤ B * ‖f s₀‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall s₀ (22/25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B) ∧
      ∀ s ∈ Metric.closedBall s₀ (83/100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
          ≤ 44795000 / R * Real.log B := by
  have hRC : (R : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hR
  set φ : ℂ → ℂ := fun w => s₀ + (R : ℂ) * w with hφ
  have hφmem : ∀ {w : ℂ} {r : ℝ}, ‖w‖ ≤ r → φ w ∈ Metric.closedBall s₀ (r * R) := by
    intro w r hw
    rw [Metric.mem_closedBall, Complex.dist_eq, hφ]
    simp only [add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    calc R * ‖w‖ ≤ R * r := mul_le_mul_of_nonneg_left hw hR.le
      _ = r * R := mul_comm _ _
  set c : ℂ := (f s₀)⁻¹ with hc
  have hcne : c ≠ 0 := inv_ne_zero hf0
  set g : ℂ → ℂ := fun w => c * f (φ w) with hg
  have hφa : ∀ w : ℂ, AnalyticAt ℂ φ w := fun w => by
    rw [hφ]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hφd : ∀ w : ℂ, deriv φ w = (R : ℂ) := by
    intro w
    rw [hφ]
    simp
  have hφinj : Function.Injective φ := by
    intro a b hab
    rw [hφ] at hab
    simp only [add_right_inj] at hab
    exact mul_left_cancel₀ hRC hab
  have hga : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro w hw
    have hwn : ‖w‖ ≤ 1 := by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hw
    have hmem : φ w ∈ Metric.closedBall s₀ R := by
      have := hφmem (r := 1) hwn
      simpa using this
    exact analyticAt_const.mul ((hfa (φ w) hmem).comp (hφa w))
  have hg0 : g 0 = 1 := by
    rw [hg, hc]
    simp only [hφ, mul_zero, add_zero]
    exact inv_mul_cancel₀ hf0
  have hg0' : g 0 ≠ 0 := by rw [hg0]; exact one_ne_zero
  have hfin : (SetOfZeros 1 g).Finite := finite_SetOfZeros hga hg0'
  have hgB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖g w‖ ≤ B := by
    intro w hw
    rw [hg]
    simp only
    rw [norm_mul, hc, norm_inv]
    rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hf0)]
    calc ‖f (φ w)‖ ≤ B * ‖f s₀‖ := hfB (φ w) (hφmem hw)
      _ = ‖f s₀‖ * B := mul_comm _ _
  have hfnezero : ∀ ρg : ℂ, g ρg = 0 ↔ f (φ ρg) = 0 := by
    intro ρg
    rw [hg]
    simp only
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hcne
      · exact h
    · intro h
      rw [h, mul_zero]
  set Zg := (finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset with hZg
  have hZgmem : ∀ ρg : ℂ, ρg ∈ Zg ↔ (‖ρg‖ ≤ 22/25 ∧ f (φ ρg) = 0) := by
    intro ρg
    rw [hZg, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hfnezero ρg).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hfnezero ρg).mpr h2⟩
  have hord : ∀ ρg : ℂ, ‖ρg‖ ≤ 1 → analyticOrderNatAt g ρg = analyticOrderNatAt f (φ ρg) := by
    intro ρg hρg
    have hcomp : analyticOrderAt (f ∘ φ) ρg = analyticOrderAt f (φ ρg) :=
      analyticOrderAt_comp_of_deriv_ne_zero (hφa ρg) (by rw [hφd]; exact hRC)
    have hsmul : analyticOrderAt g ρg = analyticOrderAt (f ∘ φ) ρg := by
      have heq : g = (fun _ : ℂ => c) • (f ∘ φ) := by
        funext w
        simp [hg, smul_eq_mul]
      rw [heq, analyticOrderAt_smul analyticAt_const
        (((hfa (φ ρg) (by simpa using hφmem (r := 1) hρg)).comp (hφa ρg)))]
      rw [(analyticAt_const (v := c)).analyticOrderAt_eq_zero.mpr hcne, zero_add]
    rw [analyticOrderNatAt, analyticOrderNatAt, hsmul, hcomp]
  refine ⟨Zg.image φ, ?_, ?_, ?_⟩
  · ext ρ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨ρg, hρg, rfl⟩
      obtain ⟨h1, h2⟩ := (hZgmem ρg).mp hρg
      exact ⟨by simpa using hφmem h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(ρ - s₀) / (R : ℂ), ?_, ?_⟩
      · rw [hZgmem]
        constructor
        · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
            div_le_iff₀ hR]
          rw [Metric.mem_closedBall, Complex.dist_eq] at h1
          linarith [h1]
        · rw [show φ ((ρ - s₀) / (R:ℂ)) = ρ by rw [hφ]; field_simp; ring]
          exact h2
      · rw [hφ]; field_simp; ring
  · have hcount := ZerosBound (by norm_num) (by norm_num)
      (by norm_num : (22/25:ℝ) < 24/25) (by norm_num) hga hg0 hfin hgB
    rw [Finset.sum_image (fun a _ b _ hab => hφinj hab)]
    have hcongr : ∀ ρg ∈ Zg, (analyticOrderNatAt f (φ ρg) : ℝ) = (analyticOrderNatAt g ρg : ℝ) := by
      intro ρg hρg
      rw [hord ρg (le_trans ((hZgmem ρg).mp hρg).1 (by norm_num))]
    rw [Finset.sum_congr rfl hcongr]
    exact_mod_cast hcount
  · intro s hs hfs
    set w : ℂ := (s - s₀) / (R : ℂ) with hw
    have hφw : φ w = s := by rw [hφ, hw]; field_simp; ring
    have hwn : ‖w‖ ≤ 83/100 := by
      rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
      rw [Metric.mem_closedBall, Complex.dist_eq] at hs
      linarith [hs]
    have hgw : g w ≠ 0 := by
      rw [hg]
      simp only
      rw [hφw]
      exact mul_ne_zero hcne hfs
    have hunit := logDeriv_partial_fraction_unit hga hg0 hfin hB2 hgB hwn hgw
    have hsR : s ∈ Metric.closedBall s₀ R :=
      Metric.closedBall_subset_closedBall (by nlinarith) hs
    have hld : logDeriv g w = (R : ℂ) * logDeriv f s := by
      have hstep : logDeriv g w = logDeriv (f ∘ φ) w := by
        rw [hg]
        exact logDeriv_const_mul w c hcne
      have hdf : DifferentiableAt ℂ f (φ w) := by
        rw [hφw]
        exact (hfa s hsR).differentiableAt
      rw [hstep, logDeriv_comp hdf (hφa w).differentiableAt, hφw, hφd, mul_comm]
    have hsum : ∑ ρ ∈ Zg.image φ, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
        = (R : ℂ)⁻¹ * ∑ ρg ∈ Zg, (analyticOrderNatAt g ρg : ℂ) / (w - ρg) := by
      rw [Finset.sum_image (fun a _ b _ hab => hφinj hab), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρg hρg => ?_
      have h34 : ‖ρg‖ ≤ 22/25 := ((hZgmem ρg).mp hρg).1
      rw [hord ρg (by linarith)]
      have hsub : s - φ ρg = (R : ℂ) * (w - ρg) := by
        rw [← hφw, hφ]
        ring
      rw [hsub]
      rw [div_mul_eq_div_div_swap]
      field_simp
    rw [hsum]
    have hfld : logDeriv f s = (R:ℂ)⁻¹ * logDeriv g w := by
      rw [hld]
      field_simp
    rw [hfld, ← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
    rw [div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hunit (inv_nonneg.mpr hR.le)

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Thm.Davenport_logDeriv_LFunction_partial_fraction
namespace SWPort
/-! Ported from prove2.me: `Davenport.logDeriv_LFunction_partial_fraction` (4953c8b0-1e84-4fc0-bbdf-aa2bf1843a47, statement by alya); proof = accepted sketch submission 318189c3-ca52-46c8-9f38-395a68078ec1 by alya. -/
























open Finset MeasureTheory Set Complex Filter Topology Asymptotics

set_option linter.unusedSectionVars false

/-!
# Partial fractions for `L'/L(s, χ)` near the line `Re s = 2` (Davenport §16, local form)

For a non-principal character `χ (mod q)` and `1 < Re s ≤ 2` we prove
`-Re (L'/L)(s, χ) ≤ c log (q (|Im s| + 2)) - ∑_{ρ ∈ Z} Re 1/(s - ρ)`
for every multiset `Z` of zeros of `L(·, χ)` in the disc `|ρ - s| ≤ 1/2`, counted with at most
their multiplicity.

The proof is the local (Borel–Carathéodory) route: the platform theorem
`Zeta23.WeilEF.logDeriv_partial_fraction_disk` gives, for an analytic function `f` on a disc
`|z - s₀| ≤ R` with `f(s₀) ≠ 0` and `|f| ≤ B |f(s₀)|` on the disc of radius `(24/25) R`,
a partial-fraction expansion of `f'/f` on the disc of radius `(83/100) R` up to an error
`≪ (log B) / R`, the sum running over the zeros in the disc of radius `(22/25) R`.

We apply it with `f = L(·, χ)`, `s₀ = 2 + i t` (`t = Im s`), `R = 2`. The two analytic inputs are
* the growth bound `|L(z, χ)| ≤ q |z| / Re z` for `Re z > 0`, from the Abel-summation
  (Mellin) representation `L(z, χ) = z ∫_1^∞ S(x) x^{-z-1} dx` with `|S(x)| ≤ q`;
* the lower bound `|L(2 + i t, χ)| ≥ 1/3` from the Dirichlet series.
-/

namespace DavenportPF

/-! ### Partial sums of a Dirichlet character (from `Sol_Davenport_deriv_LFunction_bound`) -/

variable {q : ℕ} [NeZero q]

/-- The partial character sum `S(t) = ∑_{1 ≤ k ≤ ⌊t⌋} χ(k)`. -/
noncomputable def G (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k

/-! ### The Mellin representation -/

/-- The Abel-summation integral, an analytic continuation of the L-series to `Re s > 0`. -/
noncomputable def F (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ := s * mellin (G χ) (-s)

/-! ### Analytic continuation via the identity theorem -/

/-! ### The growth bound `‖L(z, χ)‖ ≤ q ‖z‖ / Re z` -/

/-! ### The lower bound `‖L(2 + i t, χ)‖ ≥ 1/3` -/

/-! ### Facts about zeros of `L(·, χ)` -/

end DavenportPF

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_neg_logDeriv_LFunction_le_sum_zeros
namespace SWPort
/-! Ported from prove2.me: `Davenport.neg_logDeriv_LFunction_le_sum_zeros` (ebc1f4a9-b04a-4356-9fa3-3e36589066f2, statement by alya); proof = accepted sketch submission 56208df7-db43-45b6-98b5-57e452568b27 by alya. -/
























open Finset MeasureTheory Set Complex Filter Topology Asymptotics

set_option linter.unusedSectionVars false

/-!
# The zero-sum bound for `-L'/L(s, χ)` (Davenport §14, local form)

For a non-principal character `χ (mod q)` and `1 < Re s ≤ 2` we prove
`-Re (L'/L)(s, χ) ≤ c log (q (|Im s| + 2)) - ∑_{ρ ∈ Z} Re 1/(s - ρ)`
for every multiset `Z` of zeros of `L(·, χ)` in the disc `|ρ - s| ≤ 1/2`, counted with at most
their multiplicity.

The proof is the local (Borel–Carathéodory) route: the platform theorem
`Zeta23.WeilEF.logDeriv_partial_fraction_disk` gives, for an analytic function `f` on a disc
`|z - s₀| ≤ R` with `f(s₀) ≠ 0` and `|f| ≤ B |f(s₀)|` on the disc of radius `(24/25) R`,
a partial-fraction expansion of `f'/f` on the disc of radius `(83/100) R` up to an error
`≪ (log B) / R`, the sum running over the zeros in the disc of radius `(22/25) R`.

We apply it with `f = L(·, χ)`, `s₀ = 2 + i t` (`t = Im s`), `R = 2`. The two analytic inputs are
* the growth bound `|L(z, χ)| ≤ q |z| / Re z` for `Re z > 0`, from the Abel-summation
  (Mellin) representation `L(z, χ) = z ∫_1^∞ S(x) x^{-z-1} dx` with `|S(x)| ≤ q`;
* the lower bound `|L(2 + i t, χ)| ≥ 1/3` from the Dirichlet series.
-/

namespace DavenportT1

/-! ### Partial sums of a Dirichlet character (from `Sol_Davenport_deriv_LFunction_bound`) -/

variable {q : ℕ} [NeZero q]

/-- The partial character sum `S(t) = ∑_{1 ≤ k ≤ ⌊t⌋} χ(k)`. -/
noncomputable def G (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k

/-! ### The Mellin representation -/

/-- The Abel-summation integral, an analytic continuation of the L-series to `Re s > 0`. -/
noncomputable def F (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ := s * mellin (G χ) (-s)

/-! ### Analytic continuation via the identity theorem -/

/-! ### The growth bound `‖L(z, χ)‖ ≤ q ‖z‖ / Re z` -/

/-! ### The lower bound `‖L(2 + i t, χ)‖ ≥ 1/3` -/

/-! ### Facts about zeros of `L(·, χ)` -/

end DavenportT1

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_norm_LFunction_le_of_re_pos
namespace SWPort
/-! Ported from prove2.me: `Davenport.norm_LFunction_le_of_re_pos` (1b12ac8c-53f5-4d66-b458-e6adf912aa70, statement by alya); proof = accepted direct submission 2b67b00d-6837-4ca2-b83d-7017bd5b5e4a by alya. -/


















open Finset DirichletCharacter

namespace DLFB

open MeasureTheory Set Complex Filter Topology Asymptotics

/-! ### Partial sums of a Dirichlet character -/

variable {q : ℕ} [NeZero q]

/-- The partial character sum `S(t) = ∑_{1 ≤ k ≤ ⌊t⌋} χ(k)`. -/
noncomputable def G_p1 (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k

/-! ### The Mellin representation -/

/-- The Abel-summation integral, an analytic continuation of the L-series to `Re s > 0`. -/
noncomputable def F_p1 (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ := s * mellin (G_p1 χ) (-s)

/-! ### Analytic continuation via the identity theorem -/

/-! ### Bounding the Mellin integral -/

end DLFB

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_norm_LFunction_one_le
namespace SWPort
/-! Ported from prove2.me: `Davenport.norm_LFunction_one_le` (cfc76098-940a-4ab6-8f3b-192632471888, statement by alya); proof = accepted direct submission 3e67778d-9ba0-46d2-a507-5b30264ec2f9 by alya. -/


















open Finset DirichletCharacter

namespace DLFB

open MeasureTheory Set Complex Filter Topology Asymptotics

/-! ### Partial sums of a Dirichlet character -/

variable {q : ℕ} [NeZero q]

/-- The partial character sum `S(t) = ∑_{1 ≤ k ≤ ⌊t⌋} χ(k)`. -/
noncomputable def G_p2 (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k

/-! ### The Mellin representation -/

/-- The Abel-summation integral, an analytic continuation of the L-series to `Re s > 0`. -/
noncomputable def F_p2 (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ := s * mellin (G_p2 χ) (-s)

/-! ### Analytic continuation via the identity theorem -/

/-! ### Elementary real estimates -/

/-! ### Bounding the Mellin integral -/

/-! ### A numerical lower bound for `log 3` -/

end DLFB

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_perron_of_region_bound
namespace SWPort
/-! Ported from prove2.me: `Davenport.perron_of_region_bound` (e1f52231-1959-47c4-9cfb-ac1eb539c322, statement by alya); proof = accepted sketch submission ea5571ed-35e5-4b15-af08-e7266dcc30ca by alya. -/




























open Finset DirichletCharacter Vino
open Complex Real Set MeasureTheory intervalIntegral Filter Topology

namespace Davenport
namespace TP

/-! ### Piece `Sums` -/

/-! ### Helpers for (G1)/(G2) -/

/-! ### (G2) -/

/-! ### (G3) -/

/-! ### (G4) -/

/-! ### (C') -/

/-- The class-B majorant: supported on `x/2 < n < 2x`. -/
noncomputable def g_hB (N : ℕ) (x : ℝ) (n : ℕ) : ℝ :=
  if x / 2 < n ∧ (n : ℝ) < 2 * x then 8 * (1 + Real.log N) * (2 + 2 * x / |x - n|) else 0


/-! ### Piece `Kernel` -/

/-! ### Basic facts about `s ↦ y^s / s` -/


/-! ### Piece `Shift` -/

/-! ## (A) Absorption -/

/-! ## (B) Removable singularities -/

/-! ## (E) Contour shift -/


/-! ### Piece `PerronFormula` -/

/-! ### Elementary facts about `s t = σ₀ + t I` -/

/-! ### Summability of the Dirichlet series -/

/-! ### Termwise evaluation -/

/-! ### The per-term bound -/

/-! ### The truncated Perron formula -/


/-! ### Piece `Polar` -/

/-! ## Numeric facts -/

/-! ## Elementary complex facts -/

/-! ## Continuity facts -/

/-! ## The model integral `∫_{-R}^{R} du / max δ |u|` -/

/-! ## Bounds on `∫ dt/‖s‖` and `∫ dt/‖s - p‖` -/

/-! ## Case 1: `|Im p| ≤ T/2` -/

/-! ## Case 2: `|Im p| > T/2` -/

/-! ## (D) The polar terms -/

/-! ## (D') Replacing `x = N - 1/2` by `N` -/


/-! ### Piece `Assembly` -/

/-! ### Elementary real-number facts -/

/-! ### The integral identity on the line -/

/-! ### Algebraic decomposition -/

/-! ### The extension `H'` on the rectangle -/

/-! ### Bound (C): the Perron error -/

/-! ### Bound (E): the shifted integral -/

/-! ### Bound (D): the polar terms (uniform in the pole) -/

/-! ### The main bound with explicit constants -/

/-! ### The platform theorem -/


end TP
end Davenport

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_RvM_riemannZeta_linear_growth
namespace SWPort.Z
/-! Ported from prove2.me: `Zeta23.RvM.riemannZeta_linear_growth` (7e9a1251-3834-4fa2-9b09-a673b1858d26, statement by Community (Bot)); proof = accepted sketch submission c9d15889-041d-4f8b-8714-e51abf79ac9f by Community (Bot). -/





































-- from Zeta23.RvM.ZetaGrowth
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ZetaGrowth.lean — growth of ζ in vertical strips (consumed by the Landau/Jensen
local zero count and the Backlund S(T) bound).

CONTENT:
* `norm_riemannZeta_le_of_re_pos` — the explicit half-plane bound
      ‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s        (0 < Re s, s ≠ 1),
  from the N = 1 case of the summation-by-parts representation
      ζ(s) = Σ_{n≤N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx
  [Tit86, (2.1.4) / §2.1], which is `riemannZeta0` / `Zeta23_Zeta0EqZeta` in the PrimeNumberTheoremAnd
  port Zeta23/FromPNTPlus/ZetaBounds.lean (Apache-2.0, see README § Provenance).
* `riemannZeta_linear_growth` — for every δ > 0:  ‖ζ(σ+it)‖ ≤ (5/2 + δ⁻¹)·|t|  (σ ≥ δ, |t| ≥ 1)
  [Tit86, §5.1: ζ(s) = O(|t|) uniformly in σ ≥ δ], and the ∃-constant corollaries
  (`zeta_growth`, `zeta_growth_quarter`).
* `norm_riemannZeta_sub_one_le` — ‖ζ(s) − 1‖ ≤ π²/6 − 1 for Re s ≥ 2, hence the two-sided bounds
  0 < 2 − π²/6 ≤ ‖ζ(s)‖ ≤ π²/6 there (the Jensen/Landau disc centre 2 + it needs ζ ≠ 0 and a
  lower bound at the centre) [Tit86, §9.2 uses |ζ(2+iT)| ≥ … > 0].
* `analyticOnNhd_riemannZeta` — ζ is analytic on any set avoiding 1 (Mathlib's
  differentiableAt_riemannZeta, repackaged for the Jensen hypotheses).

NOT here: anything for Re s ≤ 0 (that needs the functional equation + Γ-ratio growth, i.e.
Stirling); no consumer in this repository needs it (σ ≥ 1/4 suffices).
-/

open Complex Set MeasureTheory Real

open Complex Set MeasureTheory Real

theorem _root_.SWPort.Z.Zeta23.RvM.riemannZeta_linear_growth {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hσ : δ ≤ s.re)
    (ht : 1 ≤ |s.im|) : ‖riemannZeta s‖ ≤ (5 / 2 + δ⁻¹) * |s.im| := by
  have hσpos : 0 < s.re := lt_of_lt_of_le hδ hσ
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at ht
  have h := SWPort.Z.Zeta23.RvM.norm_riemannZeta_le_of_re_pos hσpos hs1
  have him : |s.im| ≤ ‖1 - s‖ := by
    simpa using Complex.abs_im_le_norm (1 - s)
  have h1 : 1 / ‖1 - s‖ ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h2 : ‖s‖ / s.re ≤ 1 + δ⁻¹ * |s.im| := by
    have hn : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hσpos] at hn
    calc ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by gcongr
      _ = 1 + |s.im| / s.re := by field_simp
      _ ≤ 1 + |s.im| / δ := by gcongr
      _ = 1 + δ⁻¹ * |s.im| := by rw [div_eq_inv_mul]
  have h3 : (5 / 2 : ℝ) ≤ 5 / 2 * |s.im| := by nlinarith
  nlinarith [h, h1, h2, h3]

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Thm.Zeta23_WeilEF_zeta_logDeriv_partial_fraction
namespace SWPort.Z
/-! Ported from prove2.me: `Zeta23.WeilEF.zeta_logDeriv_partial_fraction` (17bc1d9d-0fcc-410c-8366-5a508c03d66d, statement by Community (Bot)); proof = accepted sketch submission 6900caa3-2aee-4601-be20-553720d58c4a by Community (Bot). -/
































































-- from Zeta23.RvM.ZetaGrowth
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ZetaGrowth.lean — growth of ζ in vertical strips (consumed by the Landau/Jensen
local zero count and the Backlund S(T) bound).

CONTENT:
* `norm_riemannZeta_le_of_re_pos` — the explicit half-plane bound
      ‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s        (0 < Re s, s ≠ 1),
  from the N = 1 case of the summation-by-parts representation
      ζ(s) = Σ_{n≤N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx
  [Tit86, (2.1.4) / §2.1], which is `riemannZeta0` / `Zeta23_Zeta0EqZeta` in the PrimeNumberTheoremAnd
  port Zeta23/FromPNTPlus/ZetaBounds.lean (Apache-2.0, see README § Provenance).
* `riemannZeta_linear_growth` — for every δ > 0:  ‖ζ(σ+it)‖ ≤ (5/2 + δ⁻¹)·|t|  (σ ≥ δ, |t| ≥ 1)
  [Tit86, §5.1: ζ(s) = O(|t|) uniformly in σ ≥ δ], and the ∃-constant corollaries
  (`zeta_growth`, `zeta_growth_quarter`).
* `norm_riemannZeta_sub_one_le` — ‖ζ(s) − 1‖ ≤ π²/6 − 1 for Re s ≥ 2, hence the two-sided bounds
  0 < 2 − π²/6 ≤ ‖ζ(s)‖ ≤ π²/6 there (the Jensen/Landau disc centre 2 + it needs ζ ≠ 0 and a
  lower bound at the centre) [Tit86, §9.2 uses |ζ(2+iT)| ≥ … > 0].
* `analyticOnNhd_riemannZeta` — ζ is analytic on any set avoiding 1 (Mathlib's
  differentiableAt_riemannZeta, repackaged for the Jensen hypotheses).

NOT here: anything for Re s ≤ 0 (that needs the functional equation + Γ-ratio growth, i.e.
Stirling); no consumer in this repository needs it (σ ≥ 1/4 suffices).
-/

open Complex Set MeasureTheory Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Analyticity away from the pole -/

/-- ζ is analytic on a neighbourhood of every set not containing 1. -/
theorem analyticOnNhd_riemannZeta {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    AnalyticOnNhd ℂ riemannZeta S := by
  have h : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  exact h.mono (Set.subset_compl_singleton_iff.mpr hS)

/-! ## The half-plane bound  [Tit86, (2.1.4) with N = 1] -/


/-! ## Linear growth in σ ≥ δ  [Tit86, §5.1] -/


/-- ∃-constant form: for every δ > 0 there is C > 0 with
‖ζ(s)‖ ≤ C·|Im s| whenever Re s ≥ δ and |Im s| ≥ 1. -/
theorem zeta_growth {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im| := by
  refine ⟨5 / 2 + δ⁻¹, by positivity, fun s hσ ht => riemannZeta_linear_growth hδ hσ ht⟩

/-- Polynomial-growth form (the shape used in Zeta23/WeilEF/Landau.lean):
∃ A C, 0 < C ∧ ∀ s, 1/4 ≤ Re s → Re s ≤ 2 → 1 ≤ |Im s| → ‖ζ s‖ ≤ C·|Im s|^A  (we give A = 1;
the upper constraint on Re s is not used). -/
theorem zeta_growth_quarter :
    ∃ A C : ℝ, 0 < C ∧ ∀ s : ℂ, (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ A := by
  obtain ⟨C, hC, h⟩ := zeta_growth (δ := 1 / 4) (by norm_num)
  refine ⟨1, C, hC, fun s h₁ _ h₃ => ?_⟩
  simpa [Real.rpow_one] using h s h₁ h₃



/-! ## Bounds on Re s ≥ 2 (the Jensen disc centre)  -/



/-- Lower bound at the Jensen disc centre: 0 < 2 − π²/6 ≤ ‖ζ(s)‖ for Re s ≥ 2. -/
theorem norm_riemannZeta_ge_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h := norm_riemannZeta_sub_one_le hs
  have h' : ‖(1 : ℂ)‖ - ‖1 - riemannZeta s‖ ≤ ‖riemannZeta s‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
  rw [norm_sub_rev] at h'
  simp only [norm_one] at h'
  linarith


/-- 1/3 < 2 − π²/6 (π < 3.15 ⇒ π²/6 < 1.654). -/
lemma one_third_lt_two_sub_pi_sq_div_six : (1 / 3 : ℝ) < 2 - Real.pi ^ 2 / 6 := by
  have := Real.pi_lt_d2
  nlinarith [Real.pi_pos]

/-- **Consumer interface.** ‖ζ(2 + it)‖ ≥ 1/3 for all real t. -/
theorem zeta_lower_bound_two : ∀ t : ℝ, (1 / 3 : ℝ) ≤ ‖riemannZeta (2 + t * I)‖ := by
  intro t
  have h := norm_riemannZeta_ge_of_two_le_re (s := 2 + t * I) (by simp)
  linarith [one_third_lt_two_sub_pi_sq_div_six]


/-- Upper bound on Re s ≥ 2: ‖ζ(s)‖ ≤ π²/6. -/
theorem norm_riemannZeta_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s‖ ≤ Real.pi ^ 2 / 6 := by
  have h := norm_riemannZeta_sub_one_le hs
  have h' : ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := by
    simpa using norm_le_norm_sub_add (riemannZeta s) (1 : ℂ)
  simp only [norm_one] at h'
  linarith

end RvM
end Zeta23
end
end

-- from Zeta23.WeilEF.Landau
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Landau.lean

Landau's lemma (Borel–Carathéodory + Jensen route; Mathlib: Analysis/Complex/BorelCaratheodory,
JensenFormula): zero counts and the partial-fraction expansion of f'/f on disks, specialized to ζ.
`zeta_local_zero_count` is consumed downstream as `RiemannVonMangoldt.local_count`.
-/

open SWPort.Z.Zeta23
open SWPort.Z.Zeta23.WeilEF
open Complex Set

theorem _root_.SWPort.Z.Zeta23.WeilEF.zeta_logDeriv_partial_fraction : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 6 ≤ |t| →
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall (2 + t * I) (22/25 * (91/50)) | riemannZeta ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (3/2), riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          ≤ C * Real.log (|t| + 3) := by
  obtain ⟨A, C₀, hC₀, hgrow⟩ := Zeta23.RvM.zeta_growth_quarter
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hCpos : (0:ℝ) < (44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) := by
    have h1 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    positivity
  refine ⟨(44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1), hCpos,
    fun t ht => ?_⟩
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hs₀im : s₀.im = t := by simp [hs₀]
  have hζs₀ : riemannZeta s₀ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₀re]; norm_num)
  have hlow : (1/3 : ℝ) ≤ ‖riemannZeta s₀‖ := Zeta23.RvM.zeta_lower_bound_two t
  -- analyticity on the closed ball of radius 91/50
  have hone : (1 : ℂ) ∉ Metric.closedBall s₀ (91/50) := by
    intro h
    rw [Metric.mem_closedBall, Complex.dist_eq] at h
    have him : ((1 : ℂ) - s₀).im = -t := by simp [hs₀]
    have : |t| ≤ ‖(1 : ℂ) - s₀‖ := by
      calc |t| = |((1:ℂ) - s₀).im| := by rw [him, abs_neg]
        _ ≤ ‖(1:ℂ) - s₀‖ := Complex.abs_im_le_norm _
    linarith
  have hfa : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₀ (91/50)) :=
    Zeta23.RvM.analyticOnNhd_riemannZeta hone
  -- the B-bound on the (24/25)·(91/50)-ball
  set B : ℝ := 3 * (C₀ * (|t| + 2) ^ A' + 2) with hB
  have ht2 : (1:ℝ) ≤ |t| + 2 := by linarith
  have hpow1 : (1:ℝ) ≤ (|t| + 2) ^ A' := Real.one_le_rpow ht2 hA'0
  have hB2 : 2 ≤ B := by
    rw [hB]
    nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one hpow1)]
  have hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * (91/50)), ‖riemannZeta w‖ ≤ B * ‖riemannZeta s₀‖ := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hwre : |w.re - 2| ≤ 24/25 * (91/50) := by
      have := Complex.abs_re_le_norm (w - s₀)
      have hre : (w - s₀).re = w.re - 2 := by simp [hs₀]
      rw [hre] at this
      linarith
    have hwim : |w.im - t| ≤ 24/25 * (91/50) := by
      have := Complex.abs_im_le_norm (w - s₀)
      have him : (w - s₀).im = w.im - t := by simp [hs₀]
      rw [him] at this
      linarith
    have hwim1 : 1 ≤ |w.im| := by
      have h3 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
      have h4 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
      linarith [hwim]
    have hwimt : |w.im| ≤ |t| + 2 := by
      have := abs_sub_abs_le_abs_sub w.im t
      have h2 : |w.im| - |t| ≤ |w.im - t| := this
      linarith [hwim]
    have hbound : ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
      rcases le_or_gt w.re 2 with hre2 | hre2
      · have h14 : (1/4 : ℝ) ≤ w.re := by
          rw [abs_le] at hwre
          linarith
        have := hgrow w h14 hre2 hwim1
        calc ‖riemannZeta w‖ ≤ C₀ * |w.im| ^ A := this
          _ ≤ C₀ * (|t| + 2) ^ A' := by
              refine mul_le_mul_of_nonneg_left ?_ hC₀.le
              calc |w.im| ^ A ≤ |w.im| ^ A' :=
                    Real.rpow_le_rpow_of_exponent_le hwim1 (le_max_left _ _)
                _ ≤ (|t| + 2) ^ A' := Real.rpow_le_rpow (by linarith) hwimt hA'0
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by linarith
      · have := Zeta23.RvM.norm_riemannZeta_le_of_two_le_re (s := w) (by linarith)
        have hπ : (Real.pi : ℝ) ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_gt_three]
        calc ‖riemannZeta w‖ ≤ Real.pi ^ 2 / 6 := this
          _ ≤ 2 := hπ
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
              nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one hpow1)]
    calc ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := hbound
      _ = (B * (1/3)) := by rw [hB]; ring
      _ ≤ B * ‖riemannZeta s₀‖ := by
          refine mul_le_mul_of_nonneg_left hlow (by rw [hB]; positivity)
  obtain ⟨Z, hZset, hZcount, hZpf⟩ := logDeriv_partial_fraction_disk (f := riemannZeta)
    (by norm_num : (0:ℝ) < 91/50) hfa hζs₀ hB2 hfB
  -- logarithmic bookkeeping shared by the count bound and the partial-fraction bound
  have hT3 : (2:ℝ) ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 9 := by norm_num
      _ ≤ |t| + 3 := by linarith
  have hlogB : Real.log B ≤ (Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3) := by
    have h1 : B ≤ 3 * ((C₀ + 2) * (|t| + 2) ^ A') := by
      rw [hB]
      nlinarith [hpow1, hC₀]
    have h2 : Real.log B ≤ Real.log (3 * ((C₀ + 2) * (|t| + 2) ^ A')) :=
      Real.log_le_log (by rw [hB]; positivity) h1
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
      Real.log_mul (by positivity : (C₀ + 2 : ℝ) ≠ 0) (by positivity),
      Real.log_rpow (by linarith : (0:ℝ) < |t| + 2)] at h2
    have h3 : Real.log (|t| + 2) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    have hBeq : Real.log B = Real.log 3 + Real.log (C₀ * (|t| + 2) ^ A' + 2) := by
      rw [hB, Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity)]
    rw [hBeq]
    nlinarith [mul_nonneg hA'0 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - Real.log (|t|+2)),
      mul_nonneg h4 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1), hT3]
  have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
  refine ⟨Z, ?_, ?_, ?_⟩
  · rw [hZset]
  · refine hZcount.trans ?_
    have hratio : ((24/25 : ℝ))/(22/25) = 12/11 := by norm_num
    have hlog1211 : (1:ℝ)/12 ≤ Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/12 by norm_num)
      rw [show (11/12:ℝ) = (12/11)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have hlogpos : (0:ℝ) < Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      exact Real.log_pos (by norm_num)
    have hlogBnn : (0:ℝ) ≤ Real.log B := Real.log_nonneg (by linarith)
    calc 1 / Real.log ((24/25)/(22/25)) * Real.log B ≤ 12 * Real.log B := by
          refine mul_le_mul_of_nonneg_right ?_ hlogBnn
          rw [div_le_iff₀ hlogpos]
          linarith
      _ ≤ 12 * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ 44795000 * 50 / 91 * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) * Real.log (|t| + 3) := by
          nlinarith [hT3, hA'0]
  · intro s hs hζs
    have hs' : s ∈ Metric.closedBall s₀ (83/100 * (91/50)) :=
      Metric.closedBall_subset_closedBall (by norm_num) hs
    refine (hZpf s hs' hζs).trans ?_
    calc 44795000 / (91/50) * Real.log B
        ≤ 44795000 / (91/50) * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ (44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) * Real.log (|t| + 3) := by
          nlinarith [hT3, hA'0]

end SWPort.Z
end

section
-- module Solutions.Artin.SW.Thm.Davenport_zero_free_region
namespace SWPort
/-! Ported from prove2.me: `Davenport.zero_free_region` (deb21296-41c0-4d78-90cb-dd1682f5a433, statement by alya); proof = accepted sketch submission 2c2d28d0-8283-4d74-8ae6-8838d91c9fdf by alya. -/
















set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset DirichletCharacter Vino

namespace Sol

open Complex

/-! ### Conjugation symmetry of Dirichlet L-functions of real characters -/

/-! ### The real-arithmetic contradictions -/

/-! ### Elementary facts about the region -/

/-! ### Abbreviations for the hypotheses coming from the child theorems -/

/-- The bound on `-L'/L` for the principal character on the real axis. -/
def TrivBound (c₀ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (σ : ℝ), 1 < σ → σ ≤ 2 →
    (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)
        / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) (σ : ℂ))).re
      ≤ 1 / (σ - 1) + c₀

/-- The bound on `-L'/L` for the principal character with the pole subtracted. -/
def PoleBound (cP : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (s : ℂ), 1 < s.re → s.re ≤ 2 →
    (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s
        / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s)).re
      ≤ (1 / (s - 1)).re + cP * Real.log ((q : ℝ) * (|s.im| + 2))

/-- The bound on `-L'/L` for a non-principal character in terms of nearby zeros. -/
def ZerosBound (cZ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      ∀ Z : Multiset ℂ, (∀ ρ ∈ Z, ‖ρ - s‖ ≤ 1 / 2) →
        (∀ ρ : ℂ, (Z.count ρ : ℕ∞) ≤ analyticOrderAt (DirichletCharacter.LFunction χ) ρ) →
          (-(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)).re
            ≤ cZ * Real.log ((q : ℝ) * (|s.im| + 2))
                - (Z.map fun ρ => (1 / (s - ρ)).re).sum

/-! ### The three zero-free arguments -/


/-! ### The principal character -/

end Sol

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_zeta_LFunction_prod_LSeries_nonneg
namespace SWPort
/-! Ported from prove2.me: `Davenport.zeta_LFunction_prod_LSeries_nonneg` (fd51d778-daa3-4513-8499-35a38fc55cf5, statement by alya); proof = accepted direct submission 8f853a15-8a1d-42f6-ae30-cdcff559f8c8 by alya. -/










open Finset DirichletCharacter

namespace SolDavenportProd

open ArithmeticFunction hiding log
open scoped ComplexOrder LSeries.notation

/-- The arithmetic function `A χ₁ χ₂ χ₁₂ = ζ ⋆ χ₁ ⋆ χ₂ ⋆ χ₁₂`. -/
noncomputable def A {N M K : ℕ} (ψ : DirichletCharacter ℂ N) (ψ' : DirichletCharacter ℂ M)
    (ψ₁₂ : DirichletCharacter ℂ K) : ArithmeticFunction ℂ :=
  zetaMul ψ * toArithmeticFunction (ψ' ·) * toArithmeticFunction (ψ₁₂ ·)

end SolDavenportProd

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_zeta_logDeriv_region_bound
namespace SWPort
/-! Ported from prove2.me: `Davenport.zeta_logDeriv_region_bound` (166af891-8983-454f-a7d7-8e883e5532f0, statement by alya); proof = accepted sketch submission 4c1aadea-2473-4804-83f8-c797c35391ea by alya. -/













open Complex

/-!
# Bound for `ζ'/ζ(s) + 1/(s-1)` in the zero-free region

Assuming `ζ` has no zeros in the region `Re s ≥ 1 - c / log (q (|Im s| + 2))`, we show
`‖ζ'/ζ(s) + 1/(s - 1)‖ ≪ log (q (|Im s| + 2))^2` for `s` in the smaller region with constant
`c / 4` and `Re s ≥ 3/4`.

For `Re s ≥ 2` this follows from the Dirichlet series of `-ζ'/ζ`.  For `3/4 ≤ Re s ≤ 2` we apply
the partial-fraction theorem `Zeta23.WeilEF.logDeriv_partial_fraction_disk` to the entire function
`g(z) = (z - 1) ζ(z)` on the disc `|z - (2 + i t)| ≤ 2`, and use the zero-free hypothesis to keep
every zero `ρ` of `g` in the disc at distance `≥ c / (4 log (q (|t| + 2)))` from `s`.
-/

namespace ZetaRegion

open Filter Topology ArithmeticFunction
open scoped LSeries.notation

/-! ### The entire function `(z - 1) ζ(z)` -/

/-- The entire function `(z - 1) ζ(z)`, with the removable singularity at `z = 1` filled in. -/
noncomputable def g : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1

/-! ### Bounds on `g` -/

/-! ### Elementary logarithm estimates -/

/-- The constant `K` with `log (300 (|t| + 2)^2) ≤ K log (q (|t| + 2))`. -/
noncomputable def K : ℝ := Real.log 300 / Real.log 2 + 2

/-! ### The core application of the partial-fraction theorem -/

/-! ### Case `3/4 ≤ Re s ≤ 2` -/

/-! ### Case `Re s ≥ 2`: the Dirichlet series -/

/-- The absolute constant `∑ Λ(n) / n²`. -/
noncomputable def M₀ : ℝ := ∑' n : ℕ, ‖LSeries.term ↗Λ 2 n‖

end ZetaRegion

end SWPort
end


