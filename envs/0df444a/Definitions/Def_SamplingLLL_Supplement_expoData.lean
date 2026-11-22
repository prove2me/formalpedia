-- Prove2me | Definitions.Def_SamplingLLL_Supplement_expoData
-- name    : SamplingLLL_Supplement_expoData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:49:03.716832+00:00
-- url     : https://prove2.me/theorems/c418ec4f-2564-4cd5-a845-bfb0340ed563
-- title:
--   Exposure Lemma: $\Gamma_v(b)$, exposure steps, (X1)–(X4), and the procedure of Appendix C
-- statement:
--   **Quantities of Definition 5.2 and Theorem 5.3**, for an atomic product-space CSP with forbidden words $\tau_a$:
--
--   - $\Gamma_v(b)=\{e\in A\setminus\{b\}: v\in\mathrm{vbl}(e),\ \tau_e(v)=\tau_b(v)\}$;
--   - an **exposure step** is a pair $(b,U)$ with $\emptyset\ne U\subsetneq\mathrm{vbl}(b)$ such that some compatible family $T\not\ni b$, connected in $H$, has $T\cup\{b\}$ compatible and $\mathrm{vbl}(b)\setminus\mathrm{vbl}(T)=U$;
--   - $\lambda_U(b)=\prod_{v\in U}\lambda_v(\tau_b(v))$, $\lambda(b)=\lambda(\mathrm{Bad}_b)$, $k_b=|\mathrm{vbl}(b)|$, $k_{\max}=\max_a k_a$;
--   - for rationals $\kappa,\beta,y_a$: $F=(1-\kappa)^{-1}$, $Y_v(b)=\prod_{e\in\Gamma_v(b)}(1-y_e)^{-1}$,
--   $$
--   B^*=\max_{a\in A}\beta\lambda(a)F^{k_a},\qquad \eta=\max_{b\in A,\ v\in\mathrm{vbl}(b)}\ \sum_{e\in\Gamma_v(b)}y_e(k_e-1).
--   $$
--
--   **Hypotheses of Theorem 5.3** (`ExposureHyp`): $\lambda(a)>0$ for all $a$; $\kappa\in(0,1)$, $\beta>0$, $K,R\in(0,1]$, $\rho\in(0,1)$, $y_a\in(0,1)$; $B^*<1$, $\eta<1$; and
--
--   1. (X1) $\sum_{a:\,v\in\mathrm{vbl}(a)}\beta\lambda(a)F^{k_a-1}\le\kappa$ for every variable $v$;
--   2. (X2) $\prod_{v\in\mathrm{vbl}(c)}Y_v(c)\le K\beta$ for every constraint $c$;
--   3. (X3) $F^{|U|}\lambda_U(b)\prod_{v\in U}Y_v(b)\le R\,y_b$ for every exposure step $(b,U)$;
--   4. (X4) $2K\ell k_{\max}\le\rho(1-B^*)(1-\eta)$ with $\ell=\log F$, the natural logarithm.
--
--   **The procedure of Appendix C**, as data for the base execution machinery: the compatible exposure exploration (C.1), the load budgets $B_{(S,c)}=\beta\lambda(c)\prod_{v\in\mathrm{vbl}(c)}\phi_v(S)^{-1}$ with $\phi_v(S)=1-\sum_{a\in S,\,v\in\mathrm{vbl}(a)}\beta\lambda(a)F^{k_a-1}$ and the variable-by-variable restoration order (C.2), the randomized-exploration proposal answering each query of $b$ yes with probability $y_b$ (C.3), and the exact local operation (C.4). The sampler is the base sequential insertion with this data and the FPRAS is the base estimator under a work cap.
--
--   **Formalization Note** The maxima $B^*$, $\eta$, $k_{\max}$ are $0$ on the empty family. The exponent $k_a-1$ in (X1) is a natural-number subtraction; it is exact, because a constraint in the sum of (X1) contains the variable $v$ and so has $k_a\ge1$. The module's main declarations are `ExposureHyp`, `expoData`, `expSampler` and `expFpras`.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Definition 5.2 and Theorem 5.3, p.16; Appendix C.1–C.4, pp.34–38

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_Common

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

variable {n m : ℕ}

/-! # The Exposure Lemma: quantities of Definition 5.2 and Theorem 5.3, and the procedure of Appendix C

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), Definition 5.2 and Theorem 5.3, p.16; Appendix C.1–C.4, pp.35–38. -/

variable (I : AtomicCSP n m)

/-- `λ_U(b) = ∏_{v∈U} λ_v(τ_b(v))` (Definition 5.2, p.16); a variable of `U` outside `vbl(b)` contributes
`1` (no exposure step has one). -/
def lamU (U : Finset (Fin n)) (b : Fin m) : ℚ :=
  ∏ v ∈ U, match I.word b v with
    | some w => I.lam v w
    | none => 1

/-- `k_b = |vbl(b)|`. -/
def kOf (b : Fin m) : ℕ := (I.vbl b).card

/-- `Γ_v(b) = {e ∈ A ∖ {b} : v ∈ vbl(e), τ_e(v) = τ_b(v)}` (Definition 5.2). -/
def GammaV (v : Fin n) (b : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun e => e ≠ b ∧ (I.word e v).isSome ∧ I.word e v = I.word b v

/-- `Y_v(b) = ∏_{e∈Γ_v(b)} (1 − y_e)^{-1}` (Theorem 5.3). -/
def Yv (y : Fin m → ℚ) (v : Fin n) (b : Fin m) : ℚ := ∏ e ∈ GammaV I v b, (1 - y e)⁻¹

/-- An exposure step `(b, U)` (Definition 5.2): `∅ ≠ U ⊊ vbl(b)`, and some compatible family `T ∌ b`,
connected in `H`, has `T ∪ {b}` compatible and `vbl(b) ∖ vbl(T) = U`. -/
def ExposureStep (b : Fin m) (U : Finset (Fin n)) : Prop :=
  U.Nonempty ∧ U ⊂ I.vbl b ∧
    ∃ T : Finset (Fin m), b ∉ T ∧ I.compat T ∧ (I.H.induce (T : Set (Fin m))).Connected ∧
      I.compat (insert b T) ∧ I.vbl b \ T.biUnion I.vbl = U

/-- `B* = max_{a∈A} β λ(a) F^{k_a}`, with `F = (1 − κ)^{-1}` (Theorem 5.3); `0` when `A = ∅`. -/
def Bstar (κ β : ℚ) : ℚ :=
  Finset.univ.fold max 0 fun a => β * I.badProb a * (1 - κ)⁻¹ ^ kOf I a

/-- `η = max_{b∈A, v∈vbl(b)} Σ_{e∈Γ_v(b)} y_e (k_e − 1)` (Theorem 5.3); `0` when `A = ∅`. -/
def eta (y : Fin m → ℚ) : ℚ :=
  Finset.univ.fold max 0 fun b =>
    (I.vbl b).fold max 0 fun v => ∑ e ∈ GammaV I v b, y e * ((kOf I e : ℚ) - 1)

/-- `k_max = max_a k_a`; `0` when `A = ∅`. -/
def kmax : ℕ := Finset.univ.fold max 0 fun a => kOf I a

/-- The hypotheses of Theorem 5.3 (p.16) on the rationals `κ, β, K, R, ρ, y`, with `F = (1−κ)^{-1}` and
`ℓ = log F` (the real natural logarithm): the ranges, `λ(a) > 0`, `B* < 1`, `η < 1`, and (X1)–(X4). -/
structure ExposureHyp (κ β K R ρ : ℚ) (y : Fin m → ℚ) : Prop where
  lam_pos : ∀ a, 0 < I.badProb a
  kappa : 0 < κ ∧ κ < 1
  beta : 0 < β
  K_mem : 0 < K ∧ K ≤ 1
  R_mem : 0 < R ∧ R ≤ 1
  rho : 0 < ρ ∧ ρ < 1
  y_mem : ∀ a, 0 < y a ∧ y a < 1
  Bstar_lt : Bstar I κ β < 1
  eta_lt : eta I y < 1
  /-- (X1) load. -/
  X1 : ∀ v : Fin n,
    ∑ a ∈ Finset.univ.filter (fun a => v ∈ I.vbl a), β * I.badProb a * (1 - κ)⁻¹ ^ (kOf I a - 1) ≤ κ
  /-- (X2) root. -/
  X2 : ∀ c : Fin m, ∏ v ∈ I.vbl c, Yv I y v c ≤ K * β
  /-- (X3) extension. -/
  X3 : ∀ (b : Fin m) (U : Finset (Fin n)), ExposureStep I b U →
    (1 - κ)⁻¹ ^ U.card * lamU I U b * ∏ v ∈ U, Yv I y v b ≤ R * y b
  /-- (X4) work. -/
  X4 : 2 * (K : ℝ) * Real.log (((1 - κ)⁻¹ : ℚ) : ℝ) * (kmax I : ℝ) ≤
    (ρ : ℝ) * (1 - (Bstar I κ β : ℝ)) * (1 - (eta I y : ℝ))

/-! ## The procedure of Appendix C -/

/-- The exposed variables `W = vbl(Y)`. -/
def expW (Y : Finset (Fin m)) : Finset (Fin n) := Y.biUnion I.vbl

/-- `b` is eligible (C.1, p.35): unqueried, `vbl(b)` meets `W` but is not contained in `W`, and `τ_b`
agrees with the fixed partial assignment `f` on `vbl(b) ∩ W`. -/
def eligible (S Y N : Finset (Fin m)) (b : Fin m) : Prop :=
  b ∈ S ∧ b ∉ Y ∧ b ∉ N ∧ (∃ v ∈ I.vbl b, v ∈ expW I Y) ∧ (∃ v ∈ I.vbl b, v ∉ expW I Y) ∧
    ∀ v ∈ I.vbl b, v ∈ expW I Y → I.word b v = I.pin Y v

instance (S Y N : Finset (Fin m)) (b : Fin m) : Decidable (eligible I S Y N b) := by
  unfold eligible; infer_instance

/-- The compatible exposure exploration of C.1, p.35: query the least eligible constraint. -/
def expNext (S : Finset (Fin m)) (_c : Fin m) : NextQuery m := fun Y N =>
  (List.finRange m).find? fun b => decide (eligible I S Y N b)

/-- `R_t = {a ∈ S : vbl(a) ∩ W_t = ∅}` (C.1, p.36). -/
def expR (S : Finset (Fin m)) (_c : Fin m) (t : Leaf m) : Finset (Fin m) :=
  S.filter fun a => Disjoint (I.vbl a) (expW I t.1)

/-- `D_t = S ∖ R_t` in the order of C.2, p.36: for `v ∈ W_t` in the order of `V`, restore, in the
constraint order, every member of `D_t` containing `v` not yet restored. -/
def expRestore (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : List (Fin m) :=
  (List.finRange n).foldl (fun acc v =>
    if v ∈ expW I t.1 then
      acc ++ (List.finRange m).filter fun a =>
        decide (a ∈ S ∧ a ∉ expR I S c t ∧ v ∈ I.vbl a ∧ a ∉ acc)
    else acc) []

/-- The record has `a_t = 0` (C.1, p.36): some unqueried member of `S` is compatible with `f_t` and
contained in `W_t`. -/
def expDead (S : Finset (Fin m)) (t : Leaf m) : Prop :=
  ∃ b ∈ S, b ∉ t.1 ∧ b ∉ t.2 ∧ I.vbl b ⊆ expW I t.1 ∧ ∀ v ∈ I.vbl b, I.word b v = I.pin t.1 v

instance (S : Finset (Fin m)) (t : Leaf m) : Decidable (expDead I S t) := by
  unfold expDead; infer_instance

/-- `E_t = {x_{W_t} = f_t}`, empty when `a_t = 0` (Lemma C.1, p.36). -/
def expEvent (S : Finset (Fin m)) (_c : Fin m) (t : Leaf m) (x : (v : Fin n) → Fin (I.dom v + 1)) :
    Bool :=
  decide (¬ expDead I S t ∧ ∀ v ∈ expW I t.1, some (x v) = I.pin t.1 v)

/-- `λ(a) = ∏_{v∈vbl(a)} λ_v(τ_a(v))`, by charged multiplications (its value is `λ(Bad_a)`). -/
def lamC (a : Fin m) : CQ :=
  cprod (((List.finRange n).filter fun v => v ∈ I.vbl a).map fun v =>
    cq (match I.word a v with
      | some w => I.lam v w
      | none => 1))

/-- `F = (1 − κ)^{-1}`, charged. -/
def FC (κ : ℚ) : CQ := cdiv (cq 1) (csub (cq 1) (cq κ))

/-- `κ_a = β λ(a) F^{k_a − 1}` (C.2, p.36), charged. -/
def kapC (κ β : ℚ) (a : Fin m) : CQ := cmul (cmul (cq β) (lamC I a)) (cpow (FC κ) (kOf I a - 1))

/-- `ϕ_v(S) = 1 − Σ_{a∈S, v∈vbl(a)} κ_a` (C.2, p.36), charged. -/
def phiC (κ β : ℚ) (S : Finset (Fin m)) (v : Fin n) : CQ :=
  csub (cq 1) (csum (((List.finRange m).filter fun a => a ∈ S ∧ v ∈ I.vbl a).map (kapC I κ β)))

/-- `B_{(S,c)} = β λ(c) ∏_{v∈vbl(c)} ϕ_v(S)^{-1}` (C.2, p.36), charged. -/
def budgetC (κ β : ℚ) (S : Finset (Fin m)) (c : Fin m) : CQ :=
  cdiv (cmul (cq β) (lamC I c))
    (cprod (((List.finRange n).filter fun v => v ∈ I.vbl c).map (phiC I κ β S)))

/-- The randomized exploration of C.3, p.37: answer each query of `b` yes with an independent coin of
bias `y_b`, tracking the probability of the path by charged operations. The fuel `m` is never
exhausted. -/
noncomputable def expRun (y : Fin m → ℚ) (L : ℕ) (S : Finset (Fin m)) (c : Fin m) :
    ℕ → Leaf m → ℚ → Proc (Leaf m × ℚ)
  | 0, t, q => pure (t, q)
  | k + 1, t, q => do
    tick (L ^ 3)
    match expNext I S c t.1 t.2 with
    | none => pure (t, q)
    | some b =>
      let yes ← ratCoin (y b)
      if yes then do
        let q' ← qmul q (y b)
        expRun y L S c k (insert b t.1, t.2) q'
      else do
        let no ← qsub 1 (y b)
        let q' ← qmul q no
        expRun y L S c k (t.1, insert b t.2) q'

/-- The proposal `q_ι` of C.3, p.37: the record reached by the randomized exploration, or the null
outcome if that record has `a_t = 0`. -/
noncomputable def expPropose (y : Fin m → ℚ) (L : ℕ) (S : Finset (Fin m)) (c : Fin m) :
    Proc (Option (Leaf m × ℚ)) := do
  let (t, q) ← expRun I y L S c m ({c}, ∅) 1
  tick (L ^ 3)
  if expDead I S t then pure none else pure (some (t, q))

/-- `acc ∏_{j∈l} s_j` with `s_j = 1 − B_j` for the child tasks `j` of a list, charged. -/
noncomputable def sChildren (κ β : ℚ) : List (Finset (Fin m) × Fin m) → ℚ → Proc ℚ
  | [], acc => pure acc
  | j :: l, acc => do
    let B ← charge (budgetC I κ β j.1 j.2)
    let s ← qsub 1 B
    let acc' ← qmul acc s
    sChildren κ β l acc'

/-- The exact local operation of C.4, p.38: thin by `a_t / [B_ι q_ι(t) ∏_{j∈C_t} s_j]`, where
`a_t = λ_{W_t}(f_t)`; on success the mark is the point mass `f_t` on `W_t` (`0` elsewhere). A record with
`a_t = 0` is rejected. -/
noncomputable def expLocal (κ β : ℚ) (L : ℕ) (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) (q : ℚ) :
    Proc (Option ((v : Fin n) → Fin (I.dom v + 1))) := do
  tick (L ^ 3)
  if expDead I S t then pure none else do
    let a ← I.uProd t.1 ((List.finRange n).filter fun v => v ∈ expW I t.1) 1
    let B ← charge (budgetC I κ β S c)
    let d0 ← qmul B q
    let den ← sChildren I κ β (chain (expRestore I S c t) (expR I S c t)) d0
    let ratio ← qdiv a den
    let keep ← ratCoin ratio
    if keep then do
      tick L
      pure (some fun v => (I.pin t.1 v).getD 0)
    else pure none

/-- The input length for Theorem 5.3: the base `inputSize` of the instance with the weights `y` as
its witnesses, plus the encodings of `κ, β, K, R, ρ`. -/
def expInputSize (κ β K R ρ : ℚ) (y : Fin m → ℚ) : ℕ :=
  I.inputSize y + bits κ + bits β + bits K + bits R + bits ρ

/-- The application data of Appendix C. Charges: `L³` per search step, `L` per constraint test and per
configuration move, `L = expInputSize`. `K`, `R`, `ρ` enter only the inputs (and the FPRAS work cap). -/
noncomputable def expoData (κ β K R ρ : ℚ) (y : Fin m → ℚ) : ExecData I.toCSP where
  next := expNext I
  rest := expR I
  restore := expRestore I
  vars _ _ t := expW I t.1
  event := expEvent I
  budget S c := (budgetC I κ β S c).1
  budgetCost S c := (budgetC I κ β S c).2
  propose := expPropose I y (expInputSize I κ β K R ρ y)
  localOp := expLocal I κ β (expInputSize I κ β K R ρ y)
  stepCost := expInputSize I κ β K R ρ y ^ 3
  testCost := expInputSize I κ β K R ρ y
  moveCost := expInputSize I κ β K R ρ y

/-- The perfect sampler of Theorem 5.3: sequential insertion with the data of Appendix C. -/
noncomputable def expSampler (κ β K R ρ : ℚ) (y : Fin m → ℚ) : Proc I.toCSP.Config :=
  (expoData I κ β K R ρ y).sampler

/-- `⌈(1−ρ)^{-1}⌉ ⌈(1−B*)^{-1}⌉`, the slack factor of Theorem 5.3. -/
def expSlack (κ β ρ : ℚ) : ℕ := ⌈(1 - ρ)⁻¹⌉₊ * ⌈(1 - Bstar I κ β)⁻¹⌉₊

/-- The FPRAS of Theorem 5.3, with the work cap `K₀ ((L + bits ε + 1) ⌈1/ε⌉ ⌈(1−ρ)^{-1}⌉ ⌈(1−B*)^{-1}⌉)^d`
of p.25 ("Cap the total work"); `K₀`, `d` are chosen once for all instances in the theorem. -/
noncomputable def expFpras (κ β K R ρ : ℚ) (y : Fin m → ℚ) (K0 d : ℕ) (ε : ℚ) : Proc ℚ :=
  (expoData I κ β K R ρ y).fpras
    (K0 * ((expInputSize I κ β K R ρ y + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊ * expSlack I κ β ρ) ^ d) ε

end SamplingLLL.Supplement


