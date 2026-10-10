-- Prove2me | Definitions.Def_ArtinMemoryModel
-- name    : ArtinMemoryModel
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T00:21:27.748689+00:00
-- url     : https://prove2.me/theorems/d776aa61-8aa6-49a9-aa1d-6d2d1e27dd35
-- title:
--   Root coordinates, the path functional, independent lines and the signed memory space of [21] §§3.5–4.8
-- statement:
--   The objects through which the moment (4.1) is proved. They build on `Def_ArtinMinorOperator`.
--
--   * Root coordinates: `tauR`, `complVec`, `ratioAt`, `detZ`, `lineOf`, `rootOf` and `physDelta`.
--   * The parameter structure `MemParams`, with `dyadParams` fixing its fields at the dyad $2^k$.
--   * The box condition `InBox`, the roots of the box `MemParams.RootIn`, and goodness `GoodAt`.
--   * The path functional `pathPhi`, through `physEdge`, `visitFac` and `physTail`, and its average over independent lines `rootIL`.
--   * The memory space $H_B$: states `stSet` with weight `stWeight`, the norm `wNorm`, and operator bounds `OpBound`.
--   * The ghost operation `ghostOp` and the edge `edgeOp = S·edgeOrd·S`.
--   * The memory moment with global birth distinctness `memMomentD`, with baseline `baseline`, which is $\prod_p b'_p$.
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), pp. 17–31, §§3.5–4.8.
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 17–31, §§3.5–4.8 (root coordinates, path functional, independent lines, signed memory space)

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
import Definitions.Def_ArtinMinorOperator

/-! # Root coordinates, independent lines and the signed memory ([21] §§3.5–4.8)

The objects through which the moment (4.1) of [21] is proved.

* **Root coordinates** ([21] (3.22), (3.30)–(3.32)). A closed physical path `P₀, P₁, …, P_N = P₀`
  is written `P_j = g z_j` with `g = (u c; v d)` the completion of `P₀`, `z₀ = z_N = e₁`. The real
  root `ω = (u, v, r)` carries the archimedean data: `(gz)₁ = u τ(z)`, `(gz)₂ = v τ(z) + z₂/u`,
  `τ(z) = z₁ + r z₂`, and the ratio of the position `gz` is `τ(w)/τ(z)` for a complement `w`.
* **The path functional** `pathPhi P ω δ`: the path expansion of `∑ ⟨u_P, (AA*)^R u_P⟩` at one
  root, with an abstract divisibility oracle `δ p z` ("`p ∣ (gz)₁`"). Physically
  `δ p z ↔ p ∣ u z₁ + c z₂` (`physDelta`); in the independent-line model `δ p z ↔ [z]_p = ℓ_p`.
* **The independent-line moment** `rootIL P ω`: `pathPhi` averaged over independent uniform
  lines `ℓ_p ∈ ℙ¹(𝔽_p)` at all group primes (`[21]` Lemma 3.4).
* **The memory space** ([21] (4.10)–(4.11)): states `(z, ℓ, m)`, `z` a primitive vector, `ℓ` the
  ordered active lists, `m` a count function on the particles `(i, p, line)` with total size
  `≤ B` (the truncation `Π_B`); weight `∏ ν(ℓ) · ∏_y λ(y)^{m(y)}/m(y)!` (the factorial measure on
  symmetric functions). The ghost `G_j` and the edge `E_j` (between slot symmetrizations) in the
  row convention, `ρ = 3/4`, `q = 1/4`.
* **Global birth distinctness** ([21] (4.14)): `memMomentD`, the same chain on states augmented
  by the set of primes born so far; a birth (initial entry, fresh target label, ghost creation)
  must be a new prime.

All sums are finite. Operators act on functions in the row convention:
`(O f)(s) = ∑_{choices} coeff · f(output)`. -/

namespace ArtinPrimitiveRoots

open Real Finset

/-! ## Root coordinates (parameter free) -/

/-- `τ(z) = z₁ + r z₂` at the real root `ω = (u, v, r)`. -/
def tauR (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) : ℝ := z.1 + ω.2.2 * z.2

/-- An integral complement `w` of a primitive `z`: `z₁ w₂ − z₂ w₁ = 1`. -/
def complVec (z : ℤ × ℤ) : ℤ × ℤ := (-Int.gcdB z.1 z.2, Int.gcdA z.1 z.2)

/-- The ratio `r_{gz} = τ(w)/τ(z) (mod 1)` of the position `gz`, [21] (3.31). -/
noncomputable def ratioAt (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) : ℝ := tauR ω (complVec z) / tauR ω z

/-- The determinant `det(z, z') = z₁ z'₂ − z₂ z'₁`. -/
def detZ (z z' : ℤ × ℤ) : ℤ := z.1 * z'.2 - z.2 * z'.1

/-- The projective line `[z]_p ∈ ℙ¹(𝔽_p)`, coded as `z₂ z₁⁻¹ mod p ∈ {0, …, p−1}` when `p ∤ z₁`
and as `p` (the line `[0 : 1]`) when `p ∣ z₁`. -/
def lineOf (p : ℕ) (z : ℤ × ℤ) : ℕ :=
  if (p : ℤ) ∣ z.1 then p else ((z.2 : ZMod p) * (z.1 : ZMod p)⁻¹).val

/-- The real root of a primitive position `P₀ = (u, v)`: `(u, v, r_{P₀})`. -/
noncomputable def rootOf (P₀ : ℕ × ℕ) : ℝ × ℝ × ℝ := (P₀.1, P₀.2, rootRatio P₀.1 P₀.2)

/-- The physical divisibility oracle at the root `P₀`: `p ∣ (g z)₁ = u z₁ + c z₂`, where
`c = (−v⁻¹ mod u)` is the top-right entry of the completion `g` of `P₀`. -/
def physDelta (P₀ : ℕ × ℕ) (p : ℕ) (z : ℤ × ℤ) : Prop :=
  (p : ℤ) ∣ (P₀.1 : ℤ) * z.1 + ((-(P₀.2 : ZMod P₀.1)⁻¹ : ZMod P₀.1).val : ℤ) * z.2

/-- The memory parameter `ρ = 3/4` ([21] (4.13): `ρ < 1`, `ρ² > √q = 1/2`). -/
noncomputable def memRho : ℝ := 3 / 4

/-! ## Parameters -/

/-- The parameters of the moment at one dyad: size `x`, groups `a`, major-arc exponent `A₀`, label
scale `Y`, `J` pads, path length `N = 2R`, pad dyad `d₀`, box scales `U`, `V`, memory bound `B`. -/
structure MemParams where
  x : ℝ
  K : ℕ
  a : Fin K → ℝ
  A₀ : ℝ
  Y : ℝ
  J : ℕ
  N : ℕ
  d₀ : ℕ
  U : ℝ
  V : ℝ
  B : ℕ

namespace MemParams

variable (P : MemParams)

/-- Ordered active lists: `J + 1` slots per group. -/
abbrev Lst := Fin P.K → Fin (P.J + 1) → ℕ

/-- The group `𝒫ᵢ`. -/
noncomputable def grp (i : Fin P.K) : Finset ℕ := primeGroup P.x (P.a i)

/-- `Vᵢ = ∑_{p ∈ 𝒫ᵢ} 1/p`. -/
noncomputable def Vg (i : Fin P.K) : ℝ := groupReciprocalSum P.x (P.a i)

/-- All group primes. -/
noncomputable def gPrimes : Finset ℕ := groupPrimes P.x P.a

/-- The damping `q_j`: `√q = 1/2` at the two ends `j = 0, N`, `q = 1/4` at interior visits. -/
noncomputable def qv (j : ℕ) : ℝ := if j = 0 ∨ j = P.N then 1 / 2 else 1 / 4

/-- `η'_j = 1 − q_j`. -/
noncomputable def etav (j : ℕ) : ℝ := 1 - P.qv j

/-- `b'_p = 1 − ∑_{j ≤ N} η'_j/(p+1)`, [21] (4.3). -/
noncomputable def bprime (p : ℕ) : ℝ := 1 - (∑ j ∈ range (P.N + 1), P.etav j) / ((p : ℝ) + 1)

/-- `νᵢ(p) = 1/(Vᵢ (p+1) b'_p)`, [21] (4.3). -/
noncomputable def nu (i : Fin P.K) (p : ℕ) : ℝ := 1 / (P.Vg i * ((p : ℝ) + 1) * P.bprime p)

/-- The extracted baseline `∏_p b'_p`. -/
noncomputable def baseline : ℝ := ∏ p ∈ P.gPrimes, P.bprime p

/-- The same parameters with memory bound `B'`. -/
def withB (B' : ℕ) : MemParams := { P with B := B' }

/-! ## Positions -/

/-- The coordinate bound of `zSet`. -/
noncomputable def zMax : ℕ := ⌈1000 * P.U * P.V⌉₊ + 1000

/-- The primitive integer vectors with coordinates `≤ zMax`. -/
noncomputable def zSet : Finset (ℤ × ℤ) :=
  ((Icc (-(P.zMax : ℤ)) P.zMax) ×ˢ (Icc (-(P.zMax : ℤ)) P.zMax)).filter
    fun z => Int.gcd z.1 z.2 = 1

/-- The box condition `g z ∈ Ω = [U,16U] × [V,2V]` at the real root `ω`, [21] (3.32). -/
def InBox (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) : Prop :=
  P.U ≤ ω.1 * tauR ω z ∧ ω.1 * tauR ω z ≤ 16 * P.U ∧
    P.V ≤ ω.2.1 * tauR ω z + z.2 / ω.1 ∧ ω.2.1 * tauR ω z + z.2 / ω.1 ≤ 2 * P.V

/-- Goodness of the position `g z` with lists `ℓ` at the root `ω`. -/
def GoodAt (ω : ℝ × ℝ × ℝ) (z : ℤ × ℤ) (ℓ : P.Lst) : Prop :=
  IsGoodRatio P.x P.Y P.a ℓ (ratioAt ω z)

/-! ## Edges -/

/-- The target list: the pads of `ℓ` (slots `< J`) and the new last labels `nw`. -/
def newList (ℓ : P.Lst) (nw : Fin P.K → ℕ) : P.Lst :=
  fun i => Fin.lastCases (nw i) (fun k => ℓ i k.castSucc)

/-- The geometric multiplier of edge `j` ([21] (3.15) without damping and normalization):
`(d₀/D) η(b/Y) η(a/Y) κ` with `κ = minorKernel(t, a, b)` on `A`-edges (`j` even) and
`κ = conj(minorKernel(−t, b, a))` on `A*`-edges (`j` odd); `b`, `a` are the source and target
unshared products and `t = det(z, z')/D`. -/
noncomputable def edgeMult (j : ℕ) (t : ℤ) (a b D : ℕ) : ℂ :=
  ((((P.d₀ : ℝ) / D) * dyadicBump ((b : ℝ) / P.Y) * dyadicBump ((a : ℝ) / P.Y) : ℝ) : ℂ) *
    (if Even j then minorKernel P.x P.A₀ P.Y t a b
      else (starRingEnd ℂ) (minorKernel P.x P.A₀ P.Y (-t) b a))

/-- The physical edge restrictions: distinct source lists, the cross-edge ban, the pad dyad,
`D ∣ det(z, z')`, the box and goodness at both ends. -/
def EdgeOK (ω : ℝ × ℝ × ℝ) (z z' : ℤ × ℤ) (ℓ : P.Lst) (nw : Fin P.K → ℕ) : Prop :=
  (∀ i, Function.Injective (ℓ i)) ∧ (∀ i, nw i ∉ Set.range (ℓ i)) ∧
    P.d₀ ≤ padProd ℓ ∧ padProd ℓ < 2 * P.d₀ ∧ (padProd ℓ : ℤ) ∣ detZ z z' ∧
    P.InBox ω z ∧ P.InBox ω z' ∧ P.GoodAt ω z ℓ ∧ P.GoodAt ω z' (P.newList ℓ nw)

/-- The slot symmetrization on lists: the average over `∏ᵢ Perm(Fin (J+1))`. -/
noncomputable def listSym (g : P.Lst → ℂ) (ℓ : P.Lst) : ℂ :=
  ((((P.J + 1).factorial ^ P.K : ℕ) : ℂ))⁻¹ *
    ∑ pr : Fin P.K → Equiv.Perm (Fin (P.J + 1)), g fun i => ℓ i ∘ pr i

/-! ## The path functional and the independent-line moment -/

open Classical in
/-- The physical edge in root coordinates (no memory): `∏Vᵢ⁻¹ × edgeMult`, target `z'` and new
labels summed with counting measure. -/
noncomputable def physEdge (ω : ℝ × ℝ × ℝ) (j : ℕ) (f : (ℤ × ℤ) × P.Lst → ℂ)
    (s : (ℤ × ℤ) × P.Lst) : ℂ :=
  ∑ z' ∈ P.zSet, ∑ nw ∈ Fintype.piFinset P.grp,
    if P.EdgeOK ω s.1 z' s.2 nw then
      ((∏ i, (P.Vg i)⁻¹ : ℝ) : ℂ) *
        P.edgeMult j (detZ s.1 z' / padProd s.2) (∏ i, nw i) (lastProd s.2) (padProd s.2) *
        f (z', P.newList s.2 nw)
    else 0

/-- `S` on functions of `(z, ℓ)`. -/
noncomputable def symP (f : (ℤ × ℤ) × P.Lst → ℂ) (s : (ℤ × ℤ) × P.Lst) : ℂ :=
  P.listSym (fun ℓ => f (s.1, ℓ)) s.2

open Classical in
/-- The factor of the group prime `p` at visit `j`: if `p` is active (in some list), it must
divide (`δ`); otherwise it pays `q_j` when it divides. -/
noncomputable def primeFac (δ : ℕ → ℤ × ℤ → Prop) (j p : ℕ) (s : (ℤ × ℤ) × P.Lst) : ℝ :=
  if ∃ i k, s.2 i k = p then (if δ p s.1 then 1 else 0) else (if δ p s.1 then P.qv j else 1)

/-- The visit factor `∏_p primeFac`. -/
noncomputable def visitFac (δ : ℕ → ℤ × ℤ → Prop) (j : ℕ) (s : (ℤ × ℤ) × P.Lst) : ℝ :=
  ∏ p ∈ P.gPrimes, P.primeFac δ j p s

/-- `physTail ω δ k f = F_{N−k} S E_{N−k} S F_{N−k+1} ⋯ S E_{N−1} S F_N f`. -/
noncomputable def physTail (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) :
    ℕ → ((ℤ × ℤ) × P.Lst → ℂ) → ((ℤ × ℤ) × P.Lst → ℂ)
  | 0, f => fun s => (P.visitFac δ P.N s : ℂ) * f s
  | k + 1, f => fun s => (P.visitFac δ (P.N - (k + 1)) s : ℂ) *
      P.symP (P.physEdge ω (P.N - (k + 1)) (P.symP (physTail ω δ k f))) s

open Classical in
/-- **The path functional** at the root `ω` with divisibility oracle `δ`: `σ ∑_{ℓ₀}` of the closed
paths from `(e₁, ℓ₀)` back to `e₁` (no return condition on the lists). -/
noncomputable def pathPhi (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) : ℂ :=
  (stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
    P.physTail ω δ P.N (fun s => if s.1 = (1, 0) then 1 else 0) ((1, 0), ℓ₀)

/-- **The independent-line moment** at the root `ω`: `pathPhi` averaged over independent uniform
lines `ℓ_p ∈ ℙ¹(𝔽_p)` (coded `0, …, p`) at all group primes. -/
noncomputable def rootIL (ω : ℝ × ℝ × ℝ) : ℂ :=
  (((∏ p ∈ P.gPrimes, ((p : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
    ∑ lam ∈ P.gPrimes.pi (fun p => range (p + 1)),
      P.pathPhi ω (fun p z => ∃ h : p ∈ P.gPrimes, lineOf p z = lam p h)

/-! ## The memory space

Memory is a count function on the finite set of particles `(i, p, line)`: `m y` copies of `y`.
This is the symmetric (bosonic) space of [21] (4.11): the factorial measure `λ^{⊗k}/k!` on
symmetric functions of `k` indexed particles is the weight `∏_y λ(y)^{m(y)}/m(y)!` on counts, and
indexed choices of `e` among `m(y)` copies count `C(m(y), e)`. An ordered birth batch with measure
`ν^{⊗l}/l!` becomes, after summing its orderings, the counts `b` with `∏_y ν(y)^{b(y)}/b(y)!`. -/

/-- All particles `(i, p, line)`, `p ∈ 𝒫ᵢ`, `line ≤ p`. -/
noncomputable def partSet : Finset (Fin P.K × ℕ × ℕ) :=
  univ.biUnion fun i => (P.grp i).biUnion fun p => (range (p + 1)).image fun l => (i, p, l)

/-- The particle type. -/
abbrev PT := {y : Fin P.K × ℕ × ℕ // y ∈ P.partSet}

/-- A memory: a count of each particle. -/
abbrev Mem := P.PT → ℕ

/-- A memory state `(z, ℓ, m)`. -/
abbrev MState := (ℤ × ℤ) × P.Lst × P.Mem

/-- The total memory size. -/
noncomputable def memSize (m : P.Mem) : ℕ := ∑ y, m y

/-- Memories of total size `≤ B` (the truncation `Π_B`). -/
noncomputable def memSet : Finset P.Mem :=
  (Fintype.piFinset fun _ => range (P.B + 1)).filter fun m => P.memSize m ≤ P.B

/-- The particle measure `λ(i, p, line) = νᵢ(p)`. -/
noncomputable def lam (y : P.PT) : ℝ := P.nu y.1.1 y.1.2.1

/-- The weight of the active lists, `∏ νᵢ(ℓᵢₖ)`. -/
noncomputable def listWeight (ℓ : P.Lst) : ℝ := ∏ i, ∏ k, P.nu i (ℓ i k)

/-- The Fock weight of a memory, `∏_y λ(y)^{m(y)}/m(y)!`. -/
noncomputable def memWeight (m : P.Mem) : ℝ := ∏ y, P.lam y ^ m y / ((m y).factorial : ℝ)

/-- The memory states. -/
noncomputable def stSet : Finset P.MState := P.zSet ×ˢ (listCands P.x P.a P.J ×ˢ P.memSet)

/-- The state weight (the measure of the Hilbert space `H_B`). -/
noncomputable def stWeight (s : P.MState) : ℝ := P.listWeight s.2.1 * P.memWeight s.2.2

/-- The particle `y` hits `z`: its anchor is `[z]_p`. -/
def IsHit (z : ℤ × ℤ) (y : P.PT) : Prop := y.1.2.2 = lineOf y.1.2.1 z

instance (z : ℤ × ℤ) (y : P.PT) : Decidable (P.IsHit z y) :=
  inferInstanceAs (Decidable (y.1.2.2 = lineOf y.1.2.1 z))

open Classical in
/-- The number of particles of `m` hitting `z`. -/
noncomputable def hitCount (z : ℤ × ℤ) (m : P.Mem) : ℕ := ∑ y, if P.IsHit z y then m y else 0

open Classical in
/-- The count of the particle `y` (zero if `y` is not a particle). -/
noncomputable def memAt (m : P.Mem) (y : Fin P.K × ℕ × ℕ) : ℕ :=
  if h : y ∈ P.partSet then m ⟨y, h⟩ else 0

/-- The weighted norm `(∑ μ(s) |f(s)|²)^{1/2}` on `H_B`. -/
noncomputable def wNorm (f : P.MState → ℂ) : ℝ := √(∑ s ∈ P.stSet, P.stWeight s * ‖f s‖ ^ 2)

/-- `O` has norm at most `C` on `H_B`. -/
def OpBound (O : (P.MState → ℂ) → (P.MState → ℂ)) (C : ℝ) : Prop :=
  ∀ f, P.wNorm (O f) ≤ C * P.wNorm f

/-! ### The ghost operation `G_j` -/

/-- Ghost choices: deletion counts and birth counts. -/
noncomputable def ghostChoices : Finset (P.Mem × P.Mem) := P.memSet ×ˢ P.memSet

open Classical in
/-- The ghost coefficient, a product over the particles hitting `z` (all others are untouched):
delete `e` of the `m(y)` copies (indexed choices `C(m(y), e)`) paying `−η'_j/ρ` each, the
survivors pay `q_j/ρ²`, and `b` new copies are born with `(−η'_j Vᵢ ν/ρ)^b/b!`. -/
noncomputable def ghostCoeff (j : ℕ) (s : P.MState) (c : P.Mem × P.Mem) : ℂ :=
  if (∀ y, c.1 y ≤ s.2.2 y) ∧ (∀ y, ¬ P.IsHit s.1 y → c.1 y = 0 ∧ c.2 y = 0) then
    ((∏ y, (if P.IsHit s.1 y then
      ((s.2.2 y).choose (c.1 y) : ℝ) * (-P.etav j / memRho) ^ c.1 y *
        (P.qv j / memRho ^ 2) ^ (s.2.2 y - c.1 y) *
        (-P.etav j * P.Vg y.1.1 / memRho) ^ c.2 y * P.lam y ^ c.2 y / ((c.2 y).factorial : ℝ)
      else 1) : ℝ) : ℂ)
  else 0

/-- The ghost output: `m − e + b`. -/
def ghostOut (s : P.MState) (c : P.Mem × P.Mem) : P.MState :=
  (s.1, s.2.1, fun y => s.2.2 y - c.1 y + c.2 y)

open Classical in
/-- **The ghost operation** `G_j` on `H_B`. -/
noncomputable def ghostOp (j : ℕ) (f : P.MState → ℂ) (s : P.MState) : ℂ :=
  ∑ c ∈ P.ghostChoices,
    P.ghostCoeff j s c * (if P.ghostOut s c ∈ P.stSet then f (P.ghostOut s c) else 0)

/-! ### The edge `E_j` -/

/-- Edge choices: the stored groups, the target position, and in each group the target's last
label with a flag "promoted from memory". -/
noncomputable def edgeChoices : Finset (Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)) :=
  univ ×ˢ (P.zSet ×ˢ Fintype.piFinset fun i => P.grp i ×ˢ univ)

/-- The particle promoted into group `i` (it must hit the target `z'`). -/
def promPart (z' : ℤ × ℤ) (tg : Fin P.K → ℕ × Bool) (i : Fin P.K) : Fin P.K × ℕ × ℕ :=
  (i, (tg i).1, lineOf (tg i).1 z')

/-- The particle stored from group `i`: the source's unshared label, anchored at `[z]_p`. -/
def storedPart (z : ℤ × ℤ) (ℓ : P.Lst) (i : Fin P.K) : Fin P.K × ℕ × ℕ :=
  (i, ℓ i (Fin.last P.J), lineOf (ℓ i (Fin.last P.J)) z)

open Classical in
/-- The number of promotions of the particle `y`. -/
noncomputable def promCount (z' : ℤ × ℤ) (tg : Fin P.K → ℕ × Bool) (y : P.PT) : ℕ :=
  (univ.filter fun i => (tg i).2 ∧ P.promPart z' tg i = y.1).card

open Classical in
/-- The number of stores of the particle `y`. -/
noncomputable def storeCount (z : ℤ × ℤ) (ℓ : P.Lst) (St : Finset (Fin P.K)) (y : P.PT) : ℕ :=
  (St.filter fun i => P.storedPart z ℓ i = y.1).card

/-- The memory after the edge: remove the promoted particles, add the stored ones. -/
noncomputable def edgeOutMem (s : P.MState)
    (c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)) : P.Mem :=
  fun y => s.2.2 y - P.promCount c.2.1 c.2.2 y + P.storeCount s.1 s.2.1 c.1 y

/-- The edge output state. -/
noncomputable def edgeOut (s : P.MState)
    (c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)) : P.MState :=
  (c.2.1, P.newList s.2.1 (fun i => (c.2.2 i).1), P.edgeOutMem s c)

open Classical in
/-- The edge coefficient ([21] §4.2 (i)–(iii)): `ρ` per old hit at the source, `count/Vᵢ` per
promotion (indexed choice; old particles only), `νᵢ` per fresh label, `ρ` per hit at the target
of the new memory, times the geometric multiplier; the physical restrictions `EdgeOK`. -/
noncomputable def edgeCoeff (ω : ℝ × ℝ × ℝ) (j : ℕ) (s : P.MState)
    (c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)) : ℂ :=
  if P.EdgeOK ω s.1 c.2.1 s.2.1 (fun i => (c.2.2 i).1) ∧
      (∀ i, (c.2.2 i).2 → P.promPart c.2.1 c.2.2 i ∈ P.partSet) ∧
      (∀ i ∈ c.1, P.storedPart s.1 s.2.1 i ∈ P.partSet) ∧
      (∀ y, P.promCount c.2.1 c.2.2 y ≤ s.2.2 y) then
    (((memRho ^ P.hitCount s.1 s.2.2 *
        (∏ i, if (c.2.2 i).2 then
          (P.memAt s.2.2 (P.promPart c.2.1 c.2.2 i) : ℝ) / P.Vg i
          else P.nu i (c.2.2 i).1) *
        memRho ^ P.hitCount c.2.1 (P.edgeOutMem s c) : ℝ) : ℂ)) *
      P.edgeMult j (detZ s.1 c.2.1 / padProd s.2.1) (∏ i, (c.2.2 i).1) (lastProd s.2.1)
        (padProd s.2.1)
  else 0

open Classical in
/-- The ordered edge (before the slot symmetrizations). -/
noncomputable def edgeOrd (ω : ℝ × ℝ × ℝ) (j : ℕ) (f : P.MState → ℂ) (s : P.MState) : ℂ :=
  ∑ c ∈ P.edgeChoices,
    P.edgeCoeff ω j s c * (if P.edgeOut s c ∈ P.stSet then f (P.edgeOut s c) else 0)

/-- `S` on functions of memory states. -/
noncomputable def symM (f : P.MState → ℂ) (s : P.MState) : ℂ :=
  P.listSym (fun ℓ => f (s.1, ℓ, s.2.2)) s.2.1

/-- **The edge** `E_j = S E_j^{ord} S` on `H_B`. -/
noncomputable def edgeOp (ω : ℝ × ℝ × ℝ) (j : ℕ) (f : P.MState → ℂ) : P.MState → ℂ :=
  P.symM (P.edgeOrd ω j (P.symM f))

/-- The boundary vector `b`: `z = e₁` and empty memory. -/
noncomputable def bVec (s : P.MState) : ℂ := if s.1 = (1, 0) ∧ s.2.2 = 0 then 1 else 0

/-! ### Global birth distinctness -/

/-- The primes born in a ghost birth count `b` (with multiplicity). -/
noncomputable def bornPrimes (b : P.Mem) : Multiset ℕ := ∑ y, b y • ({y.1.2.1} : Multiset ℕ)

/-- The fresh (not promoted) target labels. -/
def freshPrimes (tg : Fin P.K → ℕ × Bool) : List ℕ :=
  ((List.finRange P.K).filter fun i => !(tg i).2).map fun i => (tg i).1

/-- All entries of the lists. -/
def allEntries (ℓ : P.Lst) : List ℕ := (List.ofFn fun i => List.ofFn (ℓ i)).flatten

open Classical in
/-- `G_j` on states augmented by the set of born primes: births must be new and distinct. -/
noncomputable def ghostOpD (j : ℕ) (f : P.MState × Finset ℕ → ℂ) (s : P.MState × Finset ℕ) : ℂ :=
  ∑ c ∈ P.ghostChoices,
    if (P.bornPrimes c.2).Nodup ∧ ∀ p ∈ P.bornPrimes c.2, p ∉ s.2 then
      P.ghostCoeff j s.1 c * (if P.ghostOut s.1 c ∈ P.stSet then
        f (P.ghostOut s.1 c, s.2 ∪ (P.bornPrimes c.2).toFinset) else 0)
    else 0

open Classical in
/-- `E_j^{ord}` on augmented states: fresh labels must be new and distinct. -/
noncomputable def edgeOrdD (ω : ℝ × ℝ × ℝ) (j : ℕ) (f : P.MState × Finset ℕ → ℂ)
    (s : P.MState × Finset ℕ) : ℂ :=
  ∑ c ∈ P.edgeChoices,
    if (P.freshPrimes c.2.2).Nodup ∧ ∀ p ∈ P.freshPrimes c.2.2, p ∉ s.2 then
      P.edgeCoeff ω j s.1 c * (if P.edgeOut s.1 c ∈ P.stSet then
        f (P.edgeOut s.1 c, s.2 ∪ (P.freshPrimes c.2.2).toFinset) else 0)
    else 0

/-- `S` on augmented states. -/
noncomputable def symMD (f : P.MState × Finset ℕ → ℂ) (s : P.MState × Finset ℕ) : ℂ :=
  P.listSym (fun ℓ => f ((s.1.1, ℓ, s.1.2.2), s.2)) s.1.2.1

/-- `E_j` on augmented states. -/
noncomputable def edgeOpD (ω : ℝ × ℝ × ℝ) (j : ℕ) (f : P.MState × Finset ℕ → ℂ) :
    P.MState × Finset ℕ → ℂ :=
  P.symMD (P.edgeOrdD ω j (P.symMD f))

/-- `memTailD ω k f = G_{N−k} E_{N−k} ⋯ E_{N−1} G_N f` on augmented states. -/
noncomputable def memTailD (ω : ℝ × ℝ × ℝ) :
    ℕ → (P.MState × Finset ℕ → ℂ) → (P.MState × Finset ℕ → ℂ)
  | 0, f => P.ghostOpD P.N f
  | k + 1, f => P.ghostOpD (P.N - (k + 1)) (P.edgeOpD ω (P.N - (k + 1)) (memTailD ω k f))

open Classical in
/-- **The memory moment with global birth distinctness** `⟨b, G₀ E₀ G₁ ⋯ E_{N−1} G_N b⟩`,
[21] (4.14): initial active entries are births (all distinct), and every later birth is a new
prime. -/
noncomputable def memMomentD (ω : ℝ × ℝ × ℝ) : ℂ :=
  ∑ s ∈ P.stSet, if (P.allEntries s.2.1).Nodup then
    (P.stWeight s : ℂ) * P.bVec s *
      P.memTailD ω P.N (fun s' => P.bVec s'.1) (s, (P.allEntries s.2.1).toFinset)
  else 0

end MemParams

/-! ## The parameters at a dyad -/

/-- The parameters of `dyadMoment` at dyad `2^k`: `J = padCount x`, `N = 2 momentPower x`,
`U = 2^k Y H_m`, `V = H_n`, memory bound `B = ⌈L²⌉`. -/
noncomputable def dyadParams (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y Hm Hn : ℝ) (k : ℕ) :
    MemParams where
  x := x
  K := K
  a := a
  A₀ := A₀
  Y := Y
  J := padCount x
  N := 2 * momentPower x
  d₀ := 2 ^ k
  U := 2 ^ k * Y * Hm
  V := Hn
  B := ⌈log x ^ 2⌉₊

/-- The roots of the box: `ω = (u, v, r) ∈ [U,16U] × [V,2V] × [0,1]`. -/
def MemParams.RootIn (P : MemParams) (ω : ℝ × ℝ × ℝ) : Prop :=
  P.U ≤ ω.1 ∧ ω.1 ≤ 16 * P.U ∧ P.V ≤ ω.2.1 ∧ ω.2.1 ≤ 2 * P.V ∧ 0 ≤ ω.2.2 ∧ ω.2.2 ≤ 1

end ArtinPrimitiveRoots


