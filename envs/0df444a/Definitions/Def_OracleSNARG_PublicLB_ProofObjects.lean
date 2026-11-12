-- Prove2me | Definitions.Def_OracleSNARG_PublicLB_ProofObjects
-- name    : OracleSNARG_PublicLB_ProofObjects
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:47:30.675217+00:00
-- url     : https://prove2.me/theorems/05394fba-8723-4b66-8699-64dd6412e5df
-- title:
--   Proof objects of §6: $O_1$, $x_{\mathrm{crs}}$, $\pi_{\mathrm{crs},r}$, $Q_{\mathrm{crs},r}$, $I_{\mathrm{crs},r}$, pairwise-independent hashing, $O_{h,r}$, $B_{\mathrm{crs},r}$, $E_{\mathrm{crs},r}$
-- statement:
--   Fix a scheme $S=(\mathrm{Gen},P,V)$, length functions $n,N$ and $\lambda$. Below, $r\in\{0,1\}^{\text{coins}(P_\lambda)}$ is a coin vector of the honest prover.
--   - $O_1$ is the oracle answering $1$ on every query.
--   - $x_{\mathrm{crs}}=\mathrm{crs}\,\|\,1\,\|\,0^{\,n-|\mathrm{crs}|-1}$. It lies in $\{0,1\}^n$ when $|\mathrm{crs}|<n$.
--   - $\pi_{\mathrm{crs},r}=P^{O_1}_\lambda(\mathrm{crs},x_{\mathrm{crs}};r)$ is the honest prover run with every oracle answer $1$ and coins $r$.
--   - $Q_{\mathrm{crs},r}$ is the set of queries of the execution $V^{O_1}_\lambda(\mathrm{crs},x_{\mathrm{crs}},\pi_{\mathrm{crs},r})$.
--   - $I_{\mathrm{crs},r}=\{i<N:(x_{\mathrm{crs}},i)\in Q_{\mathrm{crs},r}\}$.
--
--   A **pairwise-independent family** $h:\{0,1\}^n\to\{0,1\}^k$ is a distribution $H$ on such functions satisfying two conditions:
--   - for every $x$ and $a$, $\Pr_h[h(x)=a]=2^{-k}$;
--   - for every $x\ne y$ and all $a,b$, $\Pr_h[h(x)=a\wedge h(y)=b]=2^{-2k}$.
--
--   Equation (5): for a function $h:\{0,1\}^n\to\{0,1\}^k$ and coins $r$, the oracle $O_{h,r}$ is defined on queries $(x_{\mathrm{crs}},i)$ with $|\mathrm{crs}|<n$ and $i<N$ by
--   $$O_{h,r}(x_{\mathrm{crs}},i)=\begin{cases}1,&\text{if } h(x_{\mathrm{crs}})\ne 0^k \text{ or } i\in I_{\mathrm{crs},r},\\ 0,&\text{otherwise},\end{cases}$$
--   and every other query is answered $1$.
--
--   The remaining objects are as follows.
--   - $B_{\mathrm{crs},r}=\{u\in\{0,1\}^n\setminus\{x_{\mathrm{crs}}\}:\exists i<N,\ (u,i)\in Q_{\mathrm{crs},r}\}$.
--   - $E_{\mathrm{crs},r}$ is the event (on $h$) that $h(x_{\mathrm{crs}})=0^k$ and $h(u)\ne 0^k$ for every $u\in B_{\mathrm{crs},r}$.
--   - The experiment of Equation (4) samples $\mathrm{crs}\leftarrow\mathrm{Gen}(1^\lambda)$ and uniform $r$, and outputs $V^{O_1}_\lambda(\mathrm{crs},x_{\mathrm{crs}},\pi_{\mathrm{crs},r})$.
--   - The experiment of the final display samples $h\leftarrow H$, uniform $r$ and $\mathrm{crs}\leftarrow\mathrm{Gen}(1^\lambda)$ independently. It outputs whether $C^{O_{h,r}}(x_{\mathrm{crs}})=0$ and $V^{O_{h,r}}_\lambda(\mathrm{crs},x_{\mathrm{crs}},\pi_{\mathrm{crs},r})=1$.
--
--   **Formalization Note.**
--   - Strings of length $n$ are read as vectors of $\{0,1\}^n$ through `toVec`.
--   - $0^k$ is the constant-false vector.
--   - $Q$, $I$ and $B$ are sets (`Set`), and sizes use `Set.encard`.
-- source:
--   Goldwasser, Kalai, Incrementally Verifiable Oracle Aided Computation, STOC 2027 submission (manuscript sha256 cc66f0af…), pp. 25-26, proof of Theorem 22 (Equations (4), (5); footnote 10)

import Mathlib
import Definitions.Def_OracleSNARG_PublicLB_Majority
import Definitions.Def_OracleSNARG_PublicLB_Algorithms
import Definitions.Def_OracleSNARG_PublicLB_Scheme

set_option autoImplicit false

open Classical

namespace OracleSNARG.PublicLB

/-- **The all-ones oracle** `O₁` (§6, p. 25): it answers `1` on every query. -/
def O1 : Oracle := fun _ => true

/-- **`x_crs = crs ∥ 1 ∥ 0^{n − |crs| − 1}`** (§6, p. 25). It has length `n` when `|crs| < n`. -/
def xcrs (n : ℕ) (crs : List Bool) : List Bool :=
  crs ++ true :: List.replicate (n - crs.length - 1) false

/-- **`π_{crs,r} = P^{O₁}(crs, x_crs; r)`** (§6, p. 25): the honest prover at `λ`, run with the
oracle answering every query `1` and the coin vector `r`. -/
def honestProof (S : Scheme) (n : ℕ → ℕ) (lam : ℕ) (crs : List Bool)
    (r : Fin (S.prover lam).coins → Bool) : List Bool :=
  ((S.prover lam).eval O1 [crs, xcrs (n lam) crs] r).getD 0 []

/-- The verifier's run `V(crs, x_crs, π_{crs,r})` at `λ`. -/
def verifierRun (S : Scheme) (n : ℕ → ℕ) (lam : ℕ) (crs : List Bool)
    (r : Fin (S.prover lam).coins → Bool) : QTree Bool :=
  S.verifier lam crs (xcrs (n lam) crs) (honestProof S n lam crs r)

/-- **`Q_{crs,r}`** (§6, p. 25): the set of queries made by `V` in the execution
`V^{O₁}(crs, x_crs, π_{crs,r})`. -/
def Qset (S : Scheme) (n : ℕ → ℕ) (lam : ℕ) (crs : List Bool)
    (r : Fin (S.prover lam).coins → Bool) : Set (List Bool) :=
  {u | u ∈ (verifierRun S n lam crs r).queries O1}

/-- **`I_{crs,r} = {i ∈ [N] : (x_crs, i) ∈ Q_{crs,r}}`** (§6, p. 25), positions `0, …, N − 1`. -/
def Iset (S : Scheme) (n N : ℕ → ℕ) (lam : ℕ) (crs : List Bool)
    (r : Fin (S.prover lam).coins → Bool) : Set ℕ :=
  {i | i < N lam ∧ pairEnc (xcrs (n lam) crs) i ∈ Qset S n lam crs r}

/-- **Hash functions** `h : {0,1}^n → {0,1}^k`. -/
abbrev Hash (n k : ℕ) : Type := (Fin n → Bool) → (Fin k → Bool)

/-- A bit string read as a vector of `{0,1}^n` (used on strings of length `n`). -/
def toVec (n : ℕ) (x : List Bool) : Fin n → Bool := fun i => x.getD i.val false

/-- **Pairwise-independent hash family** `h : {0,1}^n → {0,1}^k` (§6, p. 25): a distribution on
functions such that every value `h(x)` is uniform on `{0,1}^k` and, for `x ≠ y`, the pair
`(h(x), h(y))` is uniform on `{0,1}^k × {0,1}^k`. -/
def IsPairwiseIndep {n k : ℕ} (H : PMF (Hash n k)) : Prop :=
  (∀ (x : Fin n → Bool) (a : Fin k → Bool),
      H.toOuterMeasure {h | h x = a} = ((2 : ENNReal) ^ k)⁻¹) ∧
  (∀ (x y : Fin n → Bool), x ≠ y → ∀ a b : Fin k → Bool,
      H.toOuterMeasure {h | h x = a ∧ h y = b} = ((2 : ENNReal) ^ k)⁻¹ ^ 2)

/-- **The oracle `O_{h,r}`** (§6, Equation (5), p. 26) at `λ`, for a hash function `h` and prover
coins `r`: for every `crs` with `|crs| < n` and every row position `i < N`,
`O_{h,r}(x_crs, i) = 1` if `h(x_crs) ≠ 0^k` or `i ∈ I_{crs,r}`, and `0` otherwise; every query not
of this form is answered `1`. -/
noncomputable def Ohr (S : Scheme) (n N : ℕ → ℕ) (lam : ℕ) {k : ℕ} (h : Hash (n lam) k)
    (r : Fin (S.prover lam).coins → Bool) : Oracle :=
  fun u => if ∃ crs : List Bool, ∃ i : ℕ, crs.length < n lam ∧ i < N lam ∧
      u = pairEnc (xcrs (n lam) crs) i ∧ h (toVec (n lam) (xcrs (n lam) crs)) = (fun _ => false) ∧
      i ∉ Iset S n N lam crs r
    then false else true

/-- **`B_{crs,r} = {u ∈ {0,1}^n \ {x_crs} : ∃ i ∈ [N], (u, i) ∈ Q_{crs,r}}`** (§6, p. 26): the
other rows visited by `V^{O₁}(crs, x_crs, π_{crs,r})`. -/
def Bset (S : Scheme) (n N : ℕ → ℕ) (lam : ℕ) (crs : List Bool)
    (r : Fin (S.prover lam).coins → Bool) : Set (List Bool) :=
  {u | u.length = n lam ∧ u ≠ xcrs (n lam) crs ∧
    ∃ i : ℕ, i < N lam ∧ pairEnc u i ∈ Qset S n lam crs r}

/-- **The event `E_{crs,r}`** (§6, p. 26) for a hash function `h`:
`h(x_crs) = 0^k` and `h(u) ≠ 0^k` for every `u ∈ B_{crs,r}`. -/
def EventE (S : Scheme) (n N : ℕ → ℕ) (lam : ℕ) (crs : List Bool)
    (r : Fin (S.prover lam).coins → Bool) {k : ℕ} (h : Hash (n lam) k) : Prop :=
  h (toVec (n lam) (xcrs (n lam) crs)) = (fun _ => false) ∧
    ∀ u ∈ Bset S n N lam crs r, h (toVec (n lam) u) ≠ (fun _ => false)

/-- The experiment of Equation (4) (§6, p. 25) at `λ`: `crs ← Gen(1^λ)`, `r` uniform, and the
outcome `V^{O₁}(crs, x_crs, π_{crs,r})`. -/
noncomputable def eq4Exp (S : Scheme) (n : ℕ → ℕ) (lam : ℕ) : PMF Bool := do
  let crs ← S.gen lam
  let r ← PMF.uniformOfFintype (Fin (S.prover lam).coins → Bool)
  return (verifierRun S n lam crs r).eval O1

/-- The experiment of the final display (§6, p. 26) at `λ`: `h ← H`, `r` uniform and
`crs ← Gen(1^λ)`, sampled independently; the outcome is
`C^{O_{h,r}}(x_crs) = 0 ∧ V^{O_{h,r}}(crs, x_crs, π_{crs,r}) = 1`. -/
noncomputable def finalExp (S : Scheme) (n N : ℕ → ℕ) (lam : ℕ) {k : ℕ}
    (H : PMF (Hash (n lam) k)) : PMF Bool := do
  let h ← H
  let r ← PMF.uniformOfFintype (Fin (S.prover lam).coins → Bool)
  let crs ← S.gen lam
  return decide (C (Ohr S n N lam h r) (N lam) (xcrs (n lam) crs) = false ∧
    (verifierRun S n lam crs r).eval (Ohr S n N lam h r) = true)

end OracleSNARG.PublicLB


