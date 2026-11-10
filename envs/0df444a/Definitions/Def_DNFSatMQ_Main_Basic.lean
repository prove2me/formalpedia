-- Prove2me | Definitions.Def_DNFSatMQ_Main_Basic
-- name    : DNFSatMQ_Main_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:31:37.869198+00:00
-- url     : https://prove2.me/theorems/3e134681-4171-4d8a-b3e2-0c7acfe92a09
-- title:
--   Cube, conjunctions as partial assignments, DNF satisfying sets, uniform laws on {0,1}ⁿ ∪ {⊥}, Fourier coefficients on {0,1}^d
-- statement:
--   The basic objects of §2 (pp. 4–5) of the paper.
--
--   **Points and conjunctions.** A point of the cube $\{0,1\}^n$ is a map $x : \{0,\dots,n-1\} \to \{\mathsf{false},\mathsf{true}\}$ (`Pt n`), with $\mathsf{true}$ standing for the bit $1$. A **conjunction** (term) consists of literals on distinct variables; it is written as a partial assignment $c : \{0,\dots,n-1\} \to \{\text{free}, 0, 1\}$ (`Conj n`), so every term is noncontradictory and the empty conjunction is the whole cube. $x$ satisfies $c$ when it agrees with every literal. $\mathrm{Fix}(c)$ is the set of fixed coordinates, $\mathrm{Free}(c)$ its complement, the **width** is $|\mathrm{Fix}(c)|$, and $C = c^{-1}(1)$ is the set of satisfying assignments (its volume is $|C| = 2^{|\mathrm{Free}(c)|}$). $U_C$ is the uniform law on $C$; `Conj.fill c r` is the point of $C$ that copies $r$ on the free coordinates. For a point $x$ and a set $I$ of coordinates, $c_I$ fixes every $i \in I$ to $x_i$. $x^{\oplus i}$ flips coordinate $i$.
--
--   **Satisfying sets.** For a DNF $\varphi$ (the published `SamplingAC0.DNF`, a list of terms), $F = \varphi^{-1}(1)$ is `satSet φ`. For a finite set $T$ of terms, `unionSet T` $= \bigcup_{c\in T} C$; for a list $c_1,\dots,c_m$, `listUnion` is $G = \bigcup_i C_i$ and `listVolume` is $\sum_i |C_i|$.
--
--   **Laws.** For a nonempty finite $A$, $U_A$ on $\{0,1\}^n \cup \{\bot\}$ is the uniform law on $A$ pushed into `Option` by `some`, so $U_A(\bot) = 0$ (`unifBot`). `prob p E` is $\Pr_{a\sim p}[a \in E]$ as a real number. `iidLaw p N` is the law of $N$ independent draws from $p$, and `uncoveredFrac` is $\mu(\Omega \setminus G_N) = |\Omega\setminus G_N|/2^d$ for the conjunctions returned by $N$ runs (§6).
--
--   **Fourier.** $\chi_A(x) = (-1)^{\sum_{i\in A} x_i}$ and $\hat g(A) = \mathbb E_{x\sim U_d}[g(x)\chi_A(x)]$ for $g : \{0,1\}^d \to \mathbb R$ and $A \subseteq [d]$; `supDist v w` $= \max_{A} |v(A) - w(A)|$ is $\|v - w\|_\infty$; `bval` maps $\mathsf{true}, \mathsf{false}$ to $1, 0$.
--
--   **Formalization Note.** Coordinates are $0$-based. Fourier coefficients are defined locally on $\{0,1\}^d$ with the paper's character $(-1)^{\sum x_i}$, rather than reusing a $\pm1$-cube definition. Total variation is the published `SSNonExt.TV`.
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), §2 Preliminaries, p. 4 (PDF 5)

import Mathlib
import Definitions.Def_SamplingAC0_DNF
import Definitions.Def_SSNonExt_TV

namespace DNFSatMQ.Main

/-- A point of the cube `{0,1}ⁿ`, with coordinates `0, …, n-1` (the paper's `[n] = {1, …, n}`)
and `true` for the bit `1`. -/
abbrev Pt (n : ℕ) : Type := Fin n → Bool

/-- A **conjunction (term)** on `n` variables (§2, p. 4): literals on distinct variables, written
as a partial assignment. `c i = some b` means that `c` contains the literal `x_i = b`;
`c i = none` means that coordinate `i` is free. Every such term is noncontradictory, and the
empty conjunction (`fun _ => none`) represents the whole cube. -/
abbrev Conj (n : ℕ) : Type := Fin n → Option Bool

/-- `x` satisfies the conjunction `c`: it agrees with every literal of `c`. -/
def Conj.Sat {n : ℕ} (c : Conj n) (x : Pt n) : Prop :=
  ∀ i b, c i = some b → x i = b

instance {n : ℕ} (c : Conj n) (x : Pt n) : Decidable (c.Sat x) := by
  unfold Conj.Sat; infer_instance

/-- `Fix(c)`, the coordinates fixed by `c`. -/
def Conj.fix {n : ℕ} (c : Conj n) : Finset (Fin n) := Finset.univ.filter fun i => (c i).isSome

/-- `Free(c) = [n] \ Fix(c)`. -/
def Conj.free {n : ℕ} (c : Conj n) : Finset (Fin n) := Finset.univ.filter fun i => (c i).isNone

/-- The width `|Fix(c)|` of a conjunction. -/
def Conj.width {n : ℕ} (c : Conj n) : ℕ := c.fix.card

/-- `C = c⁻¹(1)`, the set of satisfying assignments of `c` (its volume is `|C| = 2^{|Free(c)|}`). -/
def Conj.cube {n : ℕ} (c : Conj n) : Finset (Pt n) := Finset.univ.filter fun x => c.Sat x

/-- The point of `C` that agrees with `r` on the free coordinates of `c` ("assigning independent
uniform bits to the coordinates free in `c`", §7, p. 26, when `r ∼ U_n`). -/
def Conj.fill {n : ℕ} (c : Conj n) (r : Pt n) : Pt n := fun i => (c i).getD (r i)

/-- `U_C`, the uniform law on the (always nonempty) set of satisfying assignments of `c`. -/
noncomputable def Conj.unif {n : ℕ} (c : Conj n) : PMF (Pt n) :=
  PMF.uniformOfFinset c.cube ⟨fun i => (c i).getD false, by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i b h => by simp [h]⟩⟩

/-- `c_I` (§5, p. 14): the conjunction fixing every coordinate `i ∈ I` to `x_i`. -/
def conjOfFix {n : ℕ} (x : Pt n) (I : Finset (Fin n)) : Conj n :=
  fun i => if i ∈ I then some (x i) else none

/-- `x^{⊕i}`, the point obtained from `x` by flipping coordinate `i` (§2, p. 4). -/
def flipAt {n : ℕ} (x : Pt n) (i : Fin n) : Pt n := Function.update x i (!x i)

/-- The satisfying set `F = f⁻¹(1)` of a DNF formula `φ` (published `SamplingAC0.DNF`). -/
def satSet {n : ℕ} (φ : SamplingAC0.DNF (Fin n)) : Finset (Pt n) :=
  Finset.univ.filter fun x => φ.eval x = true

/-- The satisfying set `⋃_{c ∈ T} C` of a DNF given as a finite set `T` of (noncontradictory)
terms. -/
def unionSet {n : ℕ} (T : Finset (Conj n)) : Finset (Pt n) :=
  Finset.univ.filter fun x => ∃ c ∈ T, c.Sat x

/-- The union `G = ⋃ᵢ Cᵢ` of the satisfying sets of a list of conjunctions. -/
def listUnion {n : ℕ} (cs : List (Conj n)) : Finset (Pt n) :=
  Finset.univ.filter fun x => ∃ c ∈ cs, c.Sat x

/-- The total volume `Σᵢ |Cᵢ|` of a list of conjunctions (with multiplicity). -/
def listVolume {n : ℕ} (cs : List (Conj n)) : ℕ := (cs.map fun c => c.cube.card).sum

/-- `U_A` on `{0,1}ⁿ ∪ {⊥}` (`Option`, with `none = ⊥`): the uniform law on the nonempty finite
set `A`, giving zero mass to `⊥` (Problem 1.1: "`U_F` and `U_H` assign zero probability to
`⊥`"). -/
noncomputable def unifBot {α : Type} (A : Finset α) (hA : A.Nonempty) : PMF (Option α) :=
  (PMF.uniformOfFinset A hA).map some

/-- The probability `Pr_{a ∼ p}[a ∈ E]` of an event, as a real number in `[0,1]`. -/
noncomputable def prob {α : Type} (p : PMF α) (E : Set α) : ℝ :=
  (p.toOuterMeasure E).toReal

/-- The character `χ_A(x) = (-1)^{Σ_{i∈A} x_i}` on `{0,1}^d` (§2, p. 4), with `x_i ∈ {0,1}`. -/
def character {d : ℕ} (A : Finset (Fin d)) (x : Pt d) : ℝ :=
  (-1 : ℝ) ^ (A.filter fun i => x i = true).card

/-- The Fourier coefficient `ĝ(A) = E_{x∼U_d}[g(x) χ_A(x)]` of `g : {0,1}^d → ℝ` (§2, p. 4). -/
noncomputable def fourierCoeff {d : ℕ} (g : Pt d → ℝ) (A : Finset (Fin d)) : ℝ :=
  (∑ x : Pt d, g x * character A x) / 2 ^ d

/-- The sup-norm distance `‖ĝ₁ − ĝ₂‖_∞ = max_{A ⊆ [d]} |ĝ₁(A) − ĝ₂(A)|` between two coefficient
vectors indexed by the subsets of `[d]`. -/
noncomputable def supDist {d : ℕ} (v w : Finset (Fin d) → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun A => |v A - w A|

/-- The joint law of `N` independent draws from `p` (`N` independent runs of a randomized
procedure whose output law is `p`). -/
noncomputable def iidLaw {α : Type} (p : PMF α) : (N : ℕ) → PMF (Fin N → α)
  | 0 => PMF.pure finZeroElim
  | N + 1 => p.bind fun a => (iidLaw p N).map fun v => Fin.cons a v

/-- `µ(Ω \ G_N)`: the fraction of `Ω = {0,1}^d` covered by none of the conjunctions returned by
`N` runs (`none` = the run returned nothing), `µ = U_d` (§6, p. 22). -/
noncomputable def uncoveredFrac {d N : ℕ} (o : Fin N → Option (Conj d)) : ℝ :=
  ((Finset.univ.filter fun z : Pt d => ∀ j c, o j = some c → ¬ c.Sat z).card : ℝ) / 2 ^ d

/-- The value of a Boolean as a real number: `true ↦ 1`, `false ↦ 0`. -/
def bval (b : Bool) : ℝ := if b then 1 else 0

end DNFSatMQ.Main


