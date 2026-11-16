-- Prove2me | Definitions.Def_MeanCertificates1424_Hardness_Supplement_Complexity
-- name    : MeanCertificates1424_Hardness_Supplement_Complexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:54:25.478472+00:00
-- url     : https://prove2.me/theorems/0ec05b5c-1191-454f-a918-fc9a6bf9f7b7
-- title:
--   Decision problems: NP, polynomial and fpt reductions into restricted classes, W[1] via p-Clique, approximation schemes, Upper-Mean, depth and radius languages
-- statement:
--   Complexity-theoretic statements use the published finite machines and binary encodings of the mission, with rational data written in binary. A **language** is a set of finite symbol strings. It is in **P** if one machine decides it within $C(|w|+1)^d$ steps, and in **NP** if membership is witnessed by a certificate of polynomial length accepted by a polynomial-time verifier. A **polynomial reduction on a class** maps every input, in polynomial time, to an input of the target that lies in the restricted class and preserves membership; **NP-hardness on a class** means every NP language reduces in this way. A language $L$ with parameter $\kappa$ is **fixed-parameter tractable** if it is decided within $f(\kappa(w))(|w|+1)^c$ steps for a computable $f$. An **fpt reduction** runs within $f(\kappa_1(w))(|w|+1)^c$ steps and bounds the new parameter by a computable function of the old one. **W[1]-hardness** is fpt-reducibility from p-Clique (a graph code followed by $k$; yes iff the graph has a $k$-clique), and **FPT = W[1]** means that p-Clique is fixed-parameter tractable. **P = NP** means that every NP language is in P.
--
--   **Upper-Mean** takes an anchored rational instance and a threshold $\theta$ and asks whether $C(y)\neq\emptyset$ and $u(y)\ge\theta$. On the published uniform unaudited instances it is restricted to the classes of Theorems 3.5 (connected split graphs of diameter at most two, $L=1$, $\epsilon=0$, $y=0$), 3.11 (connected split graphs, reports in $\{0,3\}$) and 3.12 (connected split graphs, integer reports), each with $b<n$ and, where stated, $b\le\rho n$. The **depth problem** asks whether $\Psi_G(M)\ge t$ for $0\le M<n$; the **radius problem** asks whether $R^*_\emptyset(G,b,1,0)\ge\theta$ on connected split graphs of diameter two with $2b<n$. A **relative-error approximation scheme** outputs $a$ with $|a-v|\le\xi v$; it is efficient (EPTAS) if it runs within $f(\lceil 1/\xi\rceil)(|w|+1)^c$ steps and fully polynomial (FPTAS) if within a polynomial of the input length and $1/\xi$.
--
--   These notions state the hardness results of §3.
--
--   **Formalization Note** W[1]-hardness and FPT = W[1] are expressed through p-Clique, by the standard W[1]-completeness of p-Clique. A split graph is one whose vertex set partitions into a clique and an independent set. Parameters are read off the input code (0 on strings that encode no instance).
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Section 2, Representation (printed p.6, PDF p.8); §3.2–3.4 (printed pp.9–12, PDF pp.11–14); Corollary 3.9 (printed p.10, PDF p.12)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Computation
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

namespace MeanCertificates1424.Hardness.Supplement

open MeanCertificates1424.Hardness

/-! # Decision problems, NP, W[1] and approximation schemes (printed pp.6, 9–12, PDF pp.8, 11–14)

All machines are the published finite multi-stack machines `Machine` with charged runs
`RunsWithin` on the published binary symbol encodings (separator `2`; symbol `3` is used
below only to separate an NP certificate). Rational data are encoded in binary. -/

/-- A decision problem: a set of finite symbol strings. -/
abbrev Language := List Symbol → Prop

/-- Deterministic polynomial-time decidability. -/
def InP (Lg : Language) : Prop :=
  ∃ (M : Machine) (C d : ℕ), 0 < C ∧ ∀ w, ∃ ans : Bool, (ans = true ↔ Lg w) ∧
    RunsWithin M w [if ans then 1 else 0] (C * (w.length + 1) ^ d)

/-- NP: polynomially bounded certificates checked by a polynomial-time verifier. -/
def InNP (Lg : Language) : Prop :=
  ∃ (V : Language) (C d : ℕ), InP V ∧ ∀ w,
    (Lg w ↔ ∃ cert : List Symbol, cert.length ≤ C * (w.length + 1) ^ d ∧ V (w ++ [3] ++ cert))

/-- A uniform deterministic polynomial-time computable map on strings. -/
def PolyComputable (g : List Symbol → List Symbol) : Prop :=
  ∃ (M : Machine) (C d : ℕ), 0 < C ∧ ∀ w, RunsWithin M w (g w) (C * (w.length + 1) ^ d)

/-- Polynomial-time many-one reduction from `L₁` to `L₂` all of whose outputs satisfy
`Out` (the restricted input class of the target problem). -/
def PolyReducesOn (L₁ L₂ : Language) (Out : List Symbol → Prop) : Prop :=
  ∃ g, PolyComputable g ∧ ∀ w, (L₁ w ↔ L₂ (g w)) ∧ Out (g w)

/-- NP-hardness of `L` restricted to inputs satisfying `Out`. -/
def NPHardOn (Lg : Language) (Out : List Symbol → Prop) : Prop :=
  ∀ L' : Language, InNP L' → PolyReducesOn L' Lg Out

/-- `P = NP`. -/
def PeqNP : Prop := ∀ Lg : Language, InNP Lg → InP Lg

/-- Fixed-parameter tractability: time `f(κ(w)) · (|w| + 1)^c`, `f` computable,
`c` independent of the parameter. -/
def InFPT (Lg : Language) (κ : List Symbol → ℕ) : Prop :=
  ∃ (M : Machine) (f : ℕ → ℕ) (c : ℕ), Computable f ∧ ∀ w, ∃ ans : Bool,
    (ans = true ↔ Lg w) ∧ RunsWithin M w [if ans then 1 else 0] (f (κ w) * (w.length + 1) ^ c)

/-- fpt many-one reduction with outputs in `Out`: time `f(κ₁ w)·(|w|+1)^c` and new
parameter bounded by a computable function of the old one. -/
def FptReducesOn (L₁ : Language) (κ₁ : List Symbol → ℕ) (L₂ : Language)
    (κ₂ : List Symbol → ℕ) (Out : List Symbol → Prop) : Prop :=
  ∃ (g : List Symbol → List Symbol) (M : Machine) (f h : ℕ → ℕ) (c : ℕ),
    Computable f ∧ Computable h ∧ ∀ w,
      RunsWithin M w (g w) (f (κ₁ w) * (w.length + 1) ^ c) ∧
      κ₂ (g w) ≤ h (κ₁ w) ∧ (L₁ w ↔ L₂ (g w)) ∧ Out (g w)

/-- p-Clique: a binary graph code followed by `k`, the graph having a `k`-clique. -/
def cliqueLang : Language := fun w =>
  ∃ (r : ℕ) (H : SimpleGraph (Fin r)) (k : ℕ), w = encHeadlineInput H k ∧
    ∃ s : Finset (Fin r), H.IsNClique k s

/-- Clique parameter `k` (the code is uniquely decodable; `0` on other strings). -/
noncomputable def cliqueParam (w : List Symbol) : ℕ :=
  sSup {k | ∃ (r : ℕ) (H : SimpleGraph (Fin r)), w = encHeadlineInput H k}

/-- W[1]-hardness on the restricted class `Out`, through the standard equivalence with
fpt many-one hardness from p-Clique (parameter bounded by a computable function of `k`). -/
def W1HardOn (Lg : Language) (κ : List Symbol → ℕ) (Out : List Symbol → Prop) : Prop :=
  FptReducesOn cliqueLang cliqueParam Lg κ Out

/-- `FPT = W[1]`, through the standard equivalence: p-Clique is fixed-parameter tractable. -/
def FPTeqW1 : Prop := InFPT cliqueLang cliqueParam

/-! ## Graph classes -/

/-- Split graph: the vertex set partitions into a clique and an independent set. -/
def IsSplit {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ K : Set (Fin n), G.IsClique K ∧ G.IsIndepSet Kᶜ

/-- Diameter at most two. -/
def DiamLeTwo {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v, u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

/-! ## Upper-Mean on the published rational uniform unaudited instances -/

/-- Input of Upper-Mean: instance followed by the rational threshold `θ`. -/
noncomputable def encUM (I : UniformInstance) (θ : ℚ) : List Symbol :=
  encInstance I ++ encRat θ

/-- Upper-Mean restricted to the instance class `cls`: the feasible class is nonempty and
the upper endpoint is at least `θ`. `cls` always includes validity and anchoring `b < n`. -/
def UMLang (cls : UniformInstance → Prop) : Language := fun w =>
  ∃ (I : UniformInstance) (θ : ℚ), w = encUM I θ ∧ cls I ∧ (feasible I).Nonempty ∧
    ((θ : ℝ) : EReal) ≤ Hardness.upper I

/-- Inputs of Upper-Mean whose instance lies in `cls`. -/
def UMOut (cls : UniformInstance → Prop) : List Symbol → Prop := fun w =>
  ∃ (I : UniformInstance) (θ : ℚ), w = encUM I θ ∧ cls I

/-- Parameter `b` of an Upper-Mean input (`0` on other strings). -/
noncomputable def umBudget (w : List Symbol) : ℕ :=
  sSup {b | ∃ (I : UniformInstance) (θ : ℚ), w = encUM I θ ∧ I.budget = b}

/-- Parameter `h = n − b` of an Upper-Mean input (`0` on other strings). -/
noncomputable def umHonest (w : List Symbol) : ℕ :=
  sSup {h | ∃ (I : UniformInstance) (θ : ℚ), w = encUM I θ ∧ I.n - I.budget = h}

/-- Theorem 3.5 class: connected split graphs of diameter at most two, `L = 1`, `ε = 0`,
no audits, uniform weights, `y = 0`, anchored `b < n`, and `b ≤ ρ n`
(`ρ = 1` imposes nothing beyond `b ≤ n`). -/
def ZeroSplit (ρ : ℚ) (I : UniformInstance) : Prop :=
  Hardness.Valid I ∧ I.budget < I.n ∧ IsSplit I.graph ∧ DiamLeTwo I.graph ∧ I.lipschitz = 1 ∧
  I.noise = 0 ∧ (∀ v, I.reports v = 0) ∧ (I.budget : ℚ) ≤ ρ * I.n

/-- Theorem 3.11 class: connected split graphs, reports in `{0, 3}`, `L = 1`, `ε = 0`,
no audits, uniform weights, anchored, `b ≤ ρ n`. -/
def TwoValSplit (ρ : ℚ) (I : UniformInstance) : Prop :=
  Hardness.Valid I ∧ I.budget < I.n ∧ IsSplit I.graph ∧ I.lipschitz = 1 ∧ I.noise = 0 ∧
  (∀ v, I.reports v = 0 ∨ I.reports v = 3) ∧ (I.budget : ℚ) ≤ ρ * I.n

/-- Theorem 3.12 class: connected split graphs, integer reports, `L = 1`, `ε = 0`,
no audits, uniform weights, anchored. -/
def IntSplit (I : UniformInstance) : Prop :=
  Hardness.Valid I ∧ I.budget < I.n ∧ IsSplit I.graph ∧ I.lipschitz = 1 ∧ I.noise = 0 ∧
  (∀ v, ∃ z : ℤ, I.reports v = z)

/-- `UniformInstance` → general instance (re-exported for statements). -/
noncomputable abbrev asInst (I : UniformInstance) : Inst := ofUniform I

/-! ## Hidden depth and the recovery radius as decision problems (Theorem 3.7) -/

noncomputable def encDepth {n : ℕ} (G : SimpleGraph (Fin n)) (M t : ℕ) : List Symbol :=
  encGraph G ++ encNat M ++ encNat t

/-- Is `Ψ_G(M) ≥ t`?, for `0 ≤ M < n`, on graphs in `cls`. -/
def DepthLang (cls : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ → Prop) : Language := fun w =>
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (M t : ℕ), w = encDepth G M t ∧ cls G M ∧ M < n ∧
    (t : ℕ∞) ≤ Psi G M

def DepthOut (cls : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ → Prop) : List Symbol → Prop :=
  fun w => ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (M t : ℕ), w = encDepth G M t ∧ cls G M ∧ M < n

noncomputable def depthParam (w : List Symbol) : ℕ :=
  sSup {M | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (t : ℕ), w = encDepth G M t}

/-- Connected graphs with at least one vertex (the general domain). -/
def ConnGraph {n : ℕ} (G : SimpleGraph (Fin n)) (_M : ℕ) : Prop := 1 ≤ n ∧ G.Connected

/-- Connected split graphs of diameter exactly two (published `DiameterTwo`) and even `M`. -/
def EvenSplitDiamTwo {n : ℕ} (G : SimpleGraph (Fin n)) (M : ℕ) : Prop :=
  1 ≤ n ∧ G.Connected ∧ IsSplit G ∧ DiameterTwo G ∧ Even M

noncomputable def encRad {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (θ : ℚ) : List Symbol :=
  encGraph G ++ encNat b ++ encRat θ

/-- Radius instances of Theorem 3.7: connected split graphs of diameter two, `2b < n`,
`b ≤ ρ n`. -/
def RadClass (ρ : ℚ) {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) : Prop :=
  1 ≤ n ∧ G.Connected ∧ IsSplit G ∧ DiameterTwo G ∧ 2 * b < n ∧ (b : ℚ) ≤ ρ * n

/-- Is `R*_∅(G, b, 1, 0) ≥ θ`? (uniform mean, no audits, `L = 1`, `ε = 0`). -/
def RadLang (ρ : ℚ) : Language := fun w =>
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (b : ℕ) (θ : ℚ), w = encRad G b θ ∧ RadClass ρ G b ∧
    ENNReal.ofReal θ ≤ minimaxRadius G b 1 0 ∅ (uniformW n)

def RadOut (ρ : ℚ) : List Symbol → Prop := fun w =>
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (b : ℕ) (θ : ℚ), w = encRad G b θ ∧ RadClass ρ G b

noncomputable def radParam (w : List Symbol) : ℕ :=
  sSup {b | ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (θ : ℚ), w = encRad G b θ}

/-! ## Approximation schemes (Corollary 3.9) -/

/-- Relative-error scheme with running time `f(⌈1/ξ⌉) · (input length + 1)^c`, `f`
computable: on every instance `x` of `cls` and rational `ξ > 0`, output a rational `a`
with `|a − v(x)| ≤ ξ · v(x)`. -/
def EPTAS {X : Type} (cls : X → Prop) (enc : X → List Symbol) (val : X → ℝ) : Prop :=
  ∃ (M : Machine) (f : ℕ → ℕ) (c : ℕ), Computable f ∧ ∀ x, cls x → ∀ ξ : ℚ, 0 < ξ →
    ∃ a : ℚ, RunsWithin M (enc x ++ encRat ξ) (encRat a)
        (f ⌈1 / ξ⌉₊ * ((enc x ++ encRat ξ).length + 1) ^ c) ∧
      |(a : ℝ) - val x| ≤ ξ * val x

/-- Fully polynomial scheme: time polynomial in the input length and `1/ξ`. -/
def FPTAS {X : Type} (cls : X → Prop) (enc : X → List Symbol) (val : X → ℝ) : Prop :=
  ∃ (M : Machine) (C d : ℕ), 0 < C ∧ ∀ x, cls x → ∀ ξ : ℚ, 0 < ξ →
    ∃ a : ℚ, RunsWithin M (enc x ++ encRat ξ) (encRat a)
        (C * ((enc x ++ encRat ξ).length + ⌈1 / ξ⌉₊ + 1) ^ d) ∧
      |(a : ℝ) - val x| ≤ ξ * val x

/-- A radius instance `(G, b)` as a dependent pair. -/
structure RadInst where
  n : ℕ
  G : SimpleGraph (Fin n)
  b : ℕ

end MeanCertificates1424.Hardness.Supplement


