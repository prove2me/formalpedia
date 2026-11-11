-- Prove2me | Definitions.Def_SparseWalsh_Approx_Algorithm3
-- name    : SparseWalsh_Approx_Algorithm3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:03:21.023476+00:00
-- url     : https://prove2.me/theorems/d9ea4657-420c-433d-b3a9-a1df9e2ef29e
-- title:
--   Algorithm 3 (RobustPeeling) with the parameters of Appendix D.1, as a function of its sampled objects
-- statement:
--   Algorithm 3 takes as input integers $d\ge1$ and $1\le s\le2^d$, an accuracy $\varepsilon\in(0,1]$, a method (repetition or coding), an output limit $j\in\{s,2s\}$, and, for degree-sensitive recovery, a degree bound $1\le k\le d$. It is run with a code family $E_D:\mathbb F_2^D\to\mathbb F_2^{P}$ whose correction fraction $\beta$ satisfies $0<\beta\le1/8$.
--
--   **Parameters** ((8), (9)). Write $\lceil u\rceil_2$ for $u$ rounded up to a power of two, with minimum $1$. Put
--   $$C=2^{24}/\beta,\qquad C_{\rm est}=2^{14},\qquad C_{\rm fail}=1024,\qquad R=\lceil\log_4s\rceil+1.$$
--   For each stage $r<R$:
--   $$M_r=\Big\lceil\frac{Cs}{\varepsilon2^r}\Big\rceil_2,\qquad P_r=\lceil C_{\rm est}M_r(r+1)^2\rceil_2,\qquad q_r=\lceil8\ln(128M_r(r+1)^2)\rceil,\qquad p_r=\frac1{C_{\rm fail}(r+1)^2}.$$
--   For final estimation, $U=\sum_rM_r$ and $q_{\rm fin}=\lceil8\ln(64U)\rceil$. The final tables have $P_{\rm fin}=\lceil C_{\rm est}s/\varepsilon^2\rceil_2$ buckets if $j=s$, and $P_{\rm fin}=\lceil C_{\rm est}s/\varepsilon\rceil_2$ if $j=2s$.
--
--   **Random objects**, all independent and uniform:
--   - for each stage, a hash $B_r\in\mathbb F_2^{\log_2M_r\times d}$ and an exact locator;
--   - the robust locator's base shifts;
--   - $q_r$ estimation pairs $(C,y)$ with $C\in\mathbb F_2^{\log_2P_r\times d}$;
--   - for final estimation, $q_{\rm fin}$ pairs with $\log_2P_{\rm fin}$ rows.
--
--   The exact locator is the identity locator in the general case. In the degree setting it is $n_r$ amplified copies of the Appendix C locator, with $n_r=\lceil(32/9)\ln(2/p_r)\rceil$ for repetition and $n_r=\lceil(32/9)\ln(1/p_r)\rceil$ for coding. Repetition uses $u_r=\lceil(32/9)\ln(2D_r/p_r)\rceil$ base shifts, where $D_r$ is the number of rows of the locator. Coding uses the code $E_{D_r}$ and one base shift.
--
--   **Peeling** (step 2). Start with $W_0=\emptyset$ and $w_0=0$. At stage $r$:
--   - form the residual $c_r=\hat f-w_r$;
--   - apply the robust locator to every bucket, retaining $a$ from bucket $v$ only if $B_ra=v$ (and $|a|\le k$ in the degree setting);
--   - let $V_r$ be the retained frequencies outside $W_r$;
--   - set $w_{r+1}(a)=\mathrm{Est}_{E_r}(c_r,a)$ for $a\in V_r$ and $w_{r+1}=w_r$ elsewhere, and $W_{r+1}=W_r\cup V_r$.
--
--   **Output** (step 3). Let $\tilde f(a)=\mathrm{Est}_{E_{\rm fin}}(\hat f,a)$ on $W_R$. Return the $\min\{j,|W_R|\}$ candidates of largest $|\tilde f|$ with their estimates, ties broken by the fixed order, zero coefficients omitted.
--
--   **Full-transform fallback.** If some $P_r$ or $P_{\rm fin}$ exceeds $2^d$, return the best $s$-term truncation of $\hat f$, restricted to weight at most $k$ in the degree setting.
--
--   **Formalization Note.**
--   - $\lceil u\rceil_2=2^{\lceil\log_2\lceil u\rceil\rceil}$.
--   - The random objects form one finite record with the uniform law (`randLaw`), which is the product of the independent uniform components. The record holds both methods' base shifts; a method ignores the other's, which does not change the law of its output.
--   - The residual tables are evaluated as $H^{c_r}_{B,y}$. By Lemma 3.1 and Eq. (5) these equal the tables computed from the query answers minus the contributions of $w_r$.
--   - $D_r$ is computed from the construction and does not depend on the permutations.
--   - The output is a frequency set and a coefficient vector.
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 21 (Est_E, E_r, E_fin); p. 22 (Algorithm 3); pp. 39-40 (App. D.1, Eqs. (8), (9)); pp. 40-41 (App. D.2)

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier
import Definitions.Def_SparseWalsh_Approx_Locators

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-!
# Algorithm 3 (RobustPeeling) with the parameters of Appendix D.1, as a function of its sampled
objects

Attias, Bshouty, Medvedev, Srebro, *Efficient Non-Adaptive Sparse Fourier Learning on the Boolean
Cube and Finite Abelian Groups*, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 21 (`Est_E`,
`E_r`, `E_fin`), p. 22 (Algorithm 3), pp. 39–40 (App. D.1, Eqs. (8), (9)), pp. 40–41 (App. D.2:
amplification, repetition, coding).

* Inputs: `d`, `s`, `ε`, the method (`repetition`/`coding`), the output limit (`single`: `j = s`,
  `double`: `j = 2s`) and `k` (`k = 0`: the general setting; `k ≥ 1`: the degree setting, with
  degree bound `k`). The algorithm is parameterized by a code family `codes D : BinCode D` (one
  code per message length, as Lemma D.7 supplies) and by its correction fraction `β`, which enters
  `C = 2^24/β` (App. D.1: "Fix 0 < β ≤ 1/8 no larger than the correction fraction in Lemma D.7").
* Parameters (8), (9): `⌈u⌉₂` = `u` rounded up to a power of two, minimum `1`, written as
  `2^{⌈log₂ ⌈u⌉⌉}`; `R = ⌈log₄ s⌉ + 1`; `M_r = ⌈Cs/(ε2^r)⌉₂` (hash `B_r` with `log₂ M_r` rows);
  `P_r = ⌈C_est M_r (r+1)²⌉₂`, `q_r = ⌈8 ln(128 M_r (r+1)²)⌉`, `p_r = 1/(C_fail (r+1)²)` with
  `C_est = 2^14`, `C_fail = 1024`; `U = Σ_r M_r`, `q_fin = ⌈8 ln(64U)⌉`, `P_fin = ⌈C_est s/ε²⌉₂`
  (`j = s`) or `⌈C_est s/ε⌉₂` (`j = 2s`).
* The exact locator of stage `r`: the identity locator in the general setting; in the degree
  setting `n_r` independent copies of the Appendix C locator, stacked, strict-majority decoding,
  with `n_r = ⌈(32/9) ln(2/p_r)⌉` (repetition: failure `≤ p_r/2`) or `⌈(32/9) ln(1/p_r)⌉` (coding:
  failure `≤ p_r`). `D_r` is its number of rows (independent of the permutations). Repetition uses
  `u_r = ⌈(32/9) ln(2D_r/p_r)⌉` base shifts; coding uses `codes D_r` and one base shift.
* Randomness (`Rand`): for every stage the hash `B_r`, the permutations of the `n_r` locator
  copies, `u_r` base shifts, one base shift, and the `q_r` estimation pairs `E_r`; then the `q_fin`
  final pairs `E_fin`. Every component is uniform on a finite set, and they are independent, so
  the joint law is the uniform law on `Rand` (`randLaw`). A method ignores the base shifts of the
  other method; unused independent components do not change the law of the output.
* Peeling (step 2): stage `r` forms the residual `c_r = f̂ − w_r` (the residual tables are
  `H^{c_r}_{B,y} = H^f_{B,y} − H^{w_r}_{B,y}` by Lemma 3.1 and Eq. (5)); applies the robust locator
  to every bucket `v`; retains `a` only if `B_r a = v` and, in the degree setting, `|a| ≤ k`;
  `V_r` = retained frequencies outside `W_r`; `w_{r+1}(a) = Est_{E_r}(c_r, a)` on `V_r`, otherwise
  `w_{r+1} = w_r`; `W_{r+1} = W_r ∪ V_r`.
* Output (step 3): `f̃(a) = Est_{E_fin}(f̂, a)` on `W_R`; the `min{j, |W_R|}` candidates of largest
  `|f̃|`, ties by `freqKey`; zero coefficients omitted. The output is a frequency set and a
  coefficient vector; the approximation is `Σ_{a ∈ set} coeff(a) χ_a`.
* Full-transform fallback: if some `P_r` or `P_fin` exceeds `2^d` (it suffices to check these,
  since `P_r ≥ M_r`), return the best `s`-term truncation over the allowed frequencies (`|a| ≤ k`
  in the degree setting), ties by `freqKey`, zeros omitted.
-/

/-- The frequency-identification method. -/
inductive Method | repetition | coding
  deriving DecidableEq

/-- The output limit `j ∈ {s, 2s}`. -/
inductive OutLimit | single | double
  deriving DecidableEq

/-- The number of output terms `j`. -/
def OutLimit.terms (lim : OutLimit) (s : ℕ) : ℕ :=
  match lim with
  | .single => s
  | .double => 2 * s

/-- `log₂ ⌈u⌉₂ = ⌈log₂ ⌈u⌉⌉` (so `⌈u⌉₂ = 2^{this}`, the least power of two `≥ u`, minimum `1`). -/
noncomputable def log2Ceil (u : ℝ) : ℕ := Nat.clog 2 ⌈u⌉₊

/-- `C = 2^24/β`. -/
noncomputable def bigC (β : ℝ) : ℝ := 2 ^ 24 / β

/-- `R = ⌈log₄ s⌉ + 1`. -/
def numStages (s : ℕ) : ℕ := Nat.clog 4 s + 1

/-- `log₂ M_r`: the number of rows of the location hash `B_r`. -/
noncomputable def locBits (β : ℝ) (s : ℕ) (ε : ℝ) (r : ℕ) : ℕ :=
  log2Ceil (bigC β * s / (ε * 2 ^ r))

/-- `M_r = ⌈Cs/(ε2^r)⌉₂`. -/
noncomputable def locBuckets (β : ℝ) (s : ℕ) (ε : ℝ) (r : ℕ) : ℕ := 2 ^ locBits β s ε r

/-- `log₂ P_r`, `P_r = ⌈C_est M_r (r+1)²⌉₂`, `C_est = 2^14`. -/
noncomputable def estBits (β : ℝ) (s : ℕ) (ε : ℝ) (r : ℕ) : ℕ :=
  log2Ceil (2 ^ 14 * (locBuckets β s ε r : ℝ) * ((r : ℝ) + 1) ^ 2)

/-- `q_r = ⌈8 ln(128 M_r (r+1)²)⌉`. -/
noncomputable def estCount (β : ℝ) (s : ℕ) (ε : ℝ) (r : ℕ) : ℕ :=
  ⌈8 * Real.log (128 * (locBuckets β s ε r : ℝ) * ((r : ℝ) + 1) ^ 2)⌉₊

/-- `p_r = 1/(C_fail (r+1)²)`, `C_fail = 1024`. -/
noncomputable def failParam (r : ℕ) : ℝ := 1 / (1024 * ((r : ℝ) + 1) ^ 2)

/-- `U = Σ_{r<R} M_r`. -/
noncomputable def totalBuckets (β : ℝ) (s : ℕ) (ε : ℝ) : ℕ :=
  ∑ r ∈ Finset.range (numStages s), locBuckets β s ε r

/-- `q_fin = ⌈8 ln(64U)⌉`. -/
noncomputable def finCount (β : ℝ) (s : ℕ) (ε : ℝ) : ℕ :=
  ⌈8 * Real.log (64 * (totalBuckets β s ε : ℝ))⌉₊

/-- `log₂ P_fin`, `P_fin = ⌈C_est s/ε²⌉₂` (`j = s`) or `⌈C_est s/ε⌉₂` (`j = 2s`). -/
noncomputable def finBits (s : ℕ) (ε : ℝ) (lim : OutLimit) : ℕ :=
  match lim with
  | .single => log2Ceil (2 ^ 14 * s / ε ^ 2)
  | .double => log2Ceil (2 ^ 14 * s / ε)

/-- The number of locator copies at stage `r` in the degree setting (`0` in the general
setting). -/
noncomputable def numCopies (k : ℕ) (meth : Method) (r : ℕ) : ℕ :=
  if k = 0 then 0 else
    match meth with
    | .repetition => ⌈(32 / 9 : ℝ) * Real.log (2 / failParam r)⌉₊
    | .coding => ⌈(32 / 9 : ℝ) * Real.log (1 / failParam r)⌉₊

/-- The permutations of all locator copies at stage `r`. -/
abbrev LocRand (d k : ℕ) (meth : Method) (r : ℕ) : Type :=
  Fin (numCopies k meth r) → Fin (degStages k) → Equiv.Perm (Fin (2 ^ labelBits d))

/-- The exact locator of stage `r`. -/
noncomputable def stageLocator (d k : ℕ) (meth : Method) (r : ℕ) (π : LocRand d k meth r) :
    Locator d :=
  if k = 0 then identityLocator d else stackLocators fun c => degLocator d k (π c)

/-- `D_r`: the number of rows of the stage-`r` exact locator (it does not depend on the
permutations). -/
noncomputable def stageRows (d k : ℕ) (meth : Method) (r : ℕ) : ℕ :=
  (stageLocator d k meth r fun _ _ => 1).rows.length

/-- `u_r = ⌈(32/9) ln(2D_r/p_r)⌉` base shifts for repetition. -/
noncomputable def baseShifts (d k : ℕ) (meth : Method) (r : ℕ) : ℕ :=
  ⌈(32 / 9 : ℝ) * Real.log (2 * (stageRows d k meth r : ℝ) / failParam r)⌉₊

/-- The random objects of stage `r`: location hash, locator permutations, the repetition base
shifts, the coding base shift, and the estimation pairs `E_r`. -/
abbrev StageRand (β : ℝ) (d s : ℕ) (ε : ℝ) (k : ℕ) (meth : Method) (r : ℕ) : Type :=
  Matrix (Fin (locBits β s ε r)) (Fin d) (ZMod 2) × LocRand d k meth r ×
    (Fin (baseShifts d k meth r) → Cube d) × Cube d ×
    (Fin (estCount β s ε r) → Matrix (Fin (estBits β s ε r)) (Fin d) (ZMod 2) × Cube d)

/-- All random objects of Algorithm 3. -/
abbrev Rand (β : ℝ) (d s : ℕ) (ε : ℝ) (k : ℕ) (meth : Method) (lim : OutLimit) : Type :=
  ((r : Fin (numStages s)) → StageRand β d s ε k meth r) ×
    (Fin (finCount β s ε) → Matrix (Fin (finBits s ε lim)) (Fin d) (ZMod 2) × Cube d)

/-- The law of the random objects: all components independent and uniform. -/
noncomputable def randLaw (β : ℝ) (d s : ℕ) (ε : ℝ) (k : ℕ) (meth : Method) (lim : OutLimit) :
    PMF (Rand β d s ε k meth lim) :=
  PMF.uniformOfFintype _

/-- The frequencies allowed as output: all of them (`k = 0`), or weight at most `k`. -/
def Allowed {d : ℕ} (k : ℕ) (a : Cube d) : Prop := k = 0 ∨ weight a ≤ k

/-- The candidate decoded from bucket `v` at stage `r` for the residual `c`. -/
noncomputable def stageCandidate (codes : (D : ℕ) → BinCode D) (β : ℝ) (d s : ℕ) (ε : ℝ)
    (k : ℕ) (meth : Method) (r : ℕ) (ρ : StageRand β d s ε k meth r) (c : Cube d → ℝ)
    (v : Cube (locBits β s ε r)) : Option (Cube d) :=
  let B := ρ.1
  let loc := stageLocator d k meth r ρ.2.1
  match meth with
  | .repetition => repLocate (coefBucket c B) B loc ρ.2.2.1 (Allowed k) v
  | .coding => codeLocate (coefBucket c B) B loc (codes (stageRows d k meth r)) ρ.2.2.2.1
      (Allowed k) v

/-- One peeling stage (step 2 (a)–(c)): `(W_r, w_r) ↦ (W_{r+1}, w_{r+1})`. -/
noncomputable def peelStage (codes : (D : ℕ) → BinCode D) (β : ℝ) (d s : ℕ) (ε : ℝ) (k : ℕ)
    (meth : Method) (r : ℕ) (ρ : StageRand β d s ε k meth r) (f : Cube d → ℝ)
    (Ww : Finset (Cube d) × (Cube d → ℝ)) : Finset (Cube d) × (Cube d → ℝ) := by
  classical exact
  let W := Ww.1
  let w := Ww.2
  let c : Cube d → ℝ := hat f - w
  let V : Finset (Cube d) :=
    ((Finset.univ : Finset (Cube (locBits β s ε r))).biUnion fun v =>
      (stageCandidate codes β d s ε k meth r ρ c v).toFinset) \ W
  (W ∪ V, fun a => if a ∈ V then est ρ.2.2.2.2 c a else w a)

/-- The state `(W_r, w_r)` after the first `r` peeling stages (`W_0 = ∅`, `w_0 = 0`). -/
noncomputable def peel (codes : (D : ℕ) → BinCode D) (β : ℝ) (d s : ℕ) (ε : ℝ) (k : ℕ)
    (meth : Method) (lim : OutLimit) (f : Cube d → ℝ) (ρ : Rand β d s ε k meth lim) :
    ℕ → Finset (Cube d) × (Cube d → ℝ)
  | 0 => (∅, 0)
  | r + 1 =>
      if h : r < numStages s then
        peelStage codes β d s ε k meth r (ρ.1 ⟨r, h⟩) f (peel codes β d s ε k meth lim f ρ r)
      else peel codes β d s ε k meth lim f ρ r

/-- The candidate set `W_R` after the `R` peeling stages. -/
noncomputable def candidates (codes : (D : ℕ) → BinCode D) (β : ℝ) (d s : ℕ) (ε : ℝ) (k : ℕ)
    (meth : Method) (lim : OutLimit) (f : Cube d → ℝ) (ρ : Rand β d s ε k meth lim) :
    Finset (Cube d) :=
  (peel codes β d s ε k meth lim f ρ (numStages s)).1

/-- The query points of the peeling stages: at stage `r`, the location tables at the base shifts
and at the base shifts plus the locator (repetition) or coded (coding) shifts, and the estimation
tables of `E_r`; each table is `{y + B_rᵀz}` (Eq. (3)). -/
noncomputable def peelQueryPoints (codes : (D : ℕ) → BinCode D) (β : ℝ) (d s : ℕ) (ε : ℝ)
    (k : ℕ) (meth : Method) (lim : OutLimit) (ρ : Rand β d s ε k meth lim) :
    Finset (Cube d) := by
  classical exact
  (Finset.univ : Finset (Fin (numStages s))).biUnion fun r =>
    let σ := ρ.1 r
    let B := σ.1
    let loc := stageLocator d k (meth) r σ.2.1
    let shifts : Finset (Cube d) :=
      match meth with
      | .repetition =>
          (Finset.univ : Finset (Fin (baseShifts d k meth r))).biUnion fun t =>
            insert (σ.2.2.1 t) (loc.rows.toFinset.image fun y => σ.2.2.1 t + y)
      | .coding =>
          let C := codes (stageRows d k meth r)
          let EA := C.E * locMatrix (stageRows d k meth r) loc
          insert σ.2.2.2.1 ((Finset.univ : Finset (Fin C.P)).image fun j => σ.2.2.2.1 + EA j)
    tablePoints B shifts ∪
      (Finset.univ : Finset (Fin (estCount β s ε r))).biUnion fun i =>
        tablePoints (σ.2.2.2.2 i).1 {(σ.2.2.2.2 i).2}

/-- The final estimates `f̃(a) = Est_{E_fin}(f̂, a)`. -/
noncomputable def finalEst {β : ℝ} {d s : ℕ} {ε : ℝ} {k : ℕ} {meth : Method} {lim : OutLimit}
    (f : Cube d → ℝ) (ρ : Rand β d s ε k meth lim) : Cube d → ℝ :=
  est ρ.2 (hat f)

/-- The full-transform fallback condition: some required table has more than `2^d` buckets. -/
noncomputable def fallback (β : ℝ) (d s : ℕ) (ε : ℝ) (lim : OutLimit) : Prop :=
  (∃ r < numStages s, d < estBits β s ε r) ∨ d < finBits s ε lim

/-- The output of Algorithm 3: the set of output frequencies and the coefficient vector; the
approximation is `polyOn` of the two. -/
noncomputable def algorithm3 (codes : (D : ℕ) → BinCode D) (β : ℝ) (d s : ℕ) (ε : ℝ) (k : ℕ)
    (meth : Method) (lim : OutLimit) (f : Cube d → ℝ) (ρ : Rand β d s ε k meth lim) :
    Finset (Cube d) × (Cube d → ℝ) := by
  classical exact
  if fallback β d s ε lim then
    let A := selectTop freqKey s (Finset.univ.filter fun a => Allowed k a) (hat f)
    (A.filter fun a => hat f a ≠ 0, hat f)
  else
    let ft := finalEst f ρ
    let A := selectTop freqKey (lim.terms s) (candidates codes β d s ε k meth lim f ρ) ft
    (A.filter fun a => ft a ≠ 0, ft)

end SparseWalsh.Approx


