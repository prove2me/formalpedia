-- Prove2me | Definitions.Def_QIndInf_Supplement_SolvesAvgPOVM
-- name    : QIndInf_Supplement_SolvesAvgPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:26:27.004269+00:00
-- url     : https://prove2.me/theorems/9579e5aa-cee9-44a0-8ec2-58d171194430
-- title:
--   Definition 5.4 — average-case POVM-based universal quantum inductive inference
-- statement:
--   For POVMs $M=(M_1,\dots,M_m)$, $M_j=\{E^{(j)}_x\}_x$ on $R_j$, and a state $\rho_{R_1\dots R_m}$, let
--   $$D^{M,\rho}_{\le m}(x_1,\dots,x_m)=\mathrm{Tr}\big[(E^{(1)}_{x_1}\otimes\dots\otimes E^{(m)}_{x_m})\rho_{R_1\dots R_m}\big],$$
--   let $D^{M,\rho}_{<i}$ be its marginal on the first $i-1$ coordinates and $D^{M,\rho}_i(\cdot|x_{<i})$ the conditional distribution of the $i$-th coordinate.
--
--   A quantum algorithm $L$ with classical input $(\mathsf{param}_\lambda,h_{<i},M_i)$, $h_{<i}=(M_1,x_1,\dots,M_{i-1},x_{i-1})$, and classical output **solves average-case POVM-based universal quantum inductive inference with round complexity** $r$ if for all polynomials $m,n,s,t,t',p,q$ with $m(\lambda)\ge r(\lambda,s(\lambda),p(\lambda),q(\lambda))$ and every $t'(\lambda)$-time algorithm $\mathcal G$ that on $1^\lambda$ outputs a program $T$ with $|T|\le s(\lambda)$ whose $t(\lambda)$-step run writes a circuit description of $\rho^T_{R_1\dots R_{m(\lambda)}}$, and POVMs $M_1,\dots,M_{m(\lambda)}$ described by circuits implementing them, for all sufficiently large $\lambda$
--   $$\Pr_{\substack{i\leftarrow[m],\ (T,M)\leftarrow\mathcal G(1^\lambda)\\ x_{<i}\leftarrow D^{M,\rho^T}_{<i}}}\Big[\mathrm{SD}\big(L(\mathsf{param}_\lambda,h_{<i},M_i),\ D^{M,\rho^T}_i(\cdot|x_{<i})\big)\le\frac1{p(\lambda)}\Big]\ \ge\ 1-\frac1{q(\lambda)} ,$$
--   where $\mathrm{SD}$ is the statistical distance. This is the task of Theorem 5.5; the learner sees no post-measurement state.
--
--   **Formalization Note** $D^{M,\rho}_{<i}$ is the base `outcomeProb` of the instruments $\mathcal E_x(\rho)=\mathrm{Tr}[E_x\rho]|0^n\rangle\langle0^n|$ (p.25). $\mathrm{SD}(P,Q)=\frac12\sum_w|P(w)-Q(w)|$ over all output strings $w$; outcomes of $M_i$ are its outcome bit strings. Polynomials and $\mathcal G$ are as in Definition 4.3; $r$ is an arbitrary function.
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), §5.1, Eq. (91), p.24; §5.2, Definition 5.4, Eq. (93), p.25

import Mathlib
import Definitions.Def_QIndInf_Supplement_SolvesAvg

set_option autoImplicit false

namespace QIndInf.Supplement

open QAlgorithms QAlgorithms.Complexity QAlgorithms.CopyMeasurements QiOPoQ QIndInf

/-- **A valid instance of Definition 5.4**: `z = (T, M₁, …, M_m)` with `|T| ≤ s`, `T^t` writing a
circuit description of `ρ^T`, and `m` descriptions of circuits implementing POVMs on one `n`-qubit
register each. -/
def ValidPOVMInstance (G : GateSet) (n s t m : ℕ) (z : List Bool) : Prop :=
  ∃ T ds, instParts z = some (T, ds) ∧ T.length ≤ s ∧ (srcCirc G T t).isSome ∧ ds.length = m ∧
    ∀ d ∈ ds, ValidPOVMDesc G n d

/-- **Success probability of a POVM-based learner on one instance** (the event of Eq. (93) for a
fixed `(T, M)`):
`Pr_{i ← [m], x<i ← D^{M,ρ}_{<i}} [SD(L(param, h<i, M_i), D^{M,ρ}_i(·|x<i)) ≤ 1/p]`.
`D^{M,ρ}_{<i}` is the base `outcomeProb` of the POVM instruments `E_x(ρ) = Tr[E_x ρ]|0⟩⟨0|`
(Eq. (91), p.25); the conditional distribution is
`D^{M,ρ}_i(y|x<i) = D^{M,ρ}_{≤i}(x<i, y) / D^{M,ρ}_{<i}(x<i)`, carried by the outcome strings of
`M_i`; `SD(P, Q) = ½ ∑_w |P(w) − Q(w)|` over all strings `w`. -/
noncomputable def instSuccessPOVM (G : GateSet) (L prm : List Bool) (n m p : ℕ)
    (σ : (j : ℕ) → Matrix (Regs n j) (Regs n j) ℂ) (ds : List (List Bool)) : ℝ :=
  let kx : Fin m → ℕ := fun j => (povmOf G n (ds.getD j.val [])).1
  let k : Fin m → ℕ := fun j => 2 ^ kx j
  let M : (j : Fin m) → QuantumInstrument (Reg n) (Fin (k j)) :=
    fun j => (povmOf G n (ds.getD j.val [])).2
  (1 / (m : ℝ)) * ∑ j : Fin m, ∑ x : (l : Fin j.val) → Fin (prefK k j l.castSucc),
    outcomeProb σ (pastInstr (prefI M j)) x *
      (let inp := QAdvFew.PoQOracle.tup [prm,
          histStr (fun l => ds.getD l.val [])
            (fun l => outcomeStr (k := kx (Fin.castLE (Nat.succ_le_of_lt j.isLt) l.castSucc)) (x l)),
          ds.getD j.val []]
       let cond : Fin (prefK k j (Fin.last j.val)) → ℝ := fun y =>
         outcomeProb σ (prefI M j) (Fin.snoc (α := fun l => Fin (prefK k j l)) x y) /
           outcomeProb σ (pastInstr (prefI M j)) x
       let Q : List Bool → ℝ := fun w =>
         ∑ y : Fin (prefK k j (Fin.last j.val)),
           if outcomeStr (k := kx (Fin.castLE (Nat.succ_le_of_lt j.isLt) (Fin.last j.val))) y = w
           then cond y else 0
       if (1 / 2 : ℝ) * ∑' w : List Bool, |algProb G L inp w - Q w| ≤ 1 / (p : ℝ) then 1 else 0)

/-- **Average success at security parameter `λ`** (left side of Eq. (93)): over
`(T, M) ← G(1^λ)`, `i ← [m]` and `x<i ← D^{M,ρ^T}_{<i}`. -/
noncomputable def avgSuccessPOVM (G : GateSet) (L Gd : List Bool) (lam n s t t' p q m : ℕ) : ℝ :=
  ∑' z : List Bool, algProb G Gd (unary lam) z *
    (match instParts z with
      | some (T, ds) =>
          instSuccessPOVM G L (paramStr lam n s t t' p q) n m p (srcFamily G n t T) ds
      | none => 0)

/-- **Definition 5.4 (average-case POVM-based universal quantum inductive inference).** The
algorithm `L` (classical input, classical output) solves it with round complexity `r` if for all
polynomials `m, n, s, t, t′, p, q` with `m(λ) ≥ r(λ, s(λ), p(λ), q(λ))` and every `t′(λ)`-time
algorithm `G` that on `1^λ` outputs a program `T` with `|T| ≤ s(λ)` whose `t(λ)`-step run writes a
circuit description of `ρ^T`, and POVMs `M₁, …, M_{m(λ)}` described by circuits implementing them,
for all sufficiently large `λ`:
`Pr_{i, (T,M) ← G(1^λ), x<i} [SD(L(param_λ, h<i, M_i), D^{M,ρ^T}_i(·|x<i)) ≤ 1/p(λ)] ≥ 1 − 1/q(λ)`.

arXiv:2609.36912 (PDF of 2026-11-02), §5.2, Definition 5.4, Eq. (93), p.25; distributions
Eq. (91), p.24.

**Formalization Note.** As `SolvesAvg`: `L` is used with `IsQPT L`; `m(λ), p(λ), q(λ) ≥ 1` for all sufficiently large `λ`;
`r` is any function here (Theorem 5.5 takes `r = C·(s + g(λ))·p²·q`). The learner gets no quantum
input. -/
def SolvesAvgPOVM (GS : GateSet) (L : List Bool) (r : ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (m n s t t' p q : Polynomial ℕ),
    (∀ᶠ lam in Filter.atTop, 1 ≤ m.eval lam) → (∀ᶠ lam in Filter.atTop, 1 ≤ p.eval lam) →
    (∀ᶠ lam in Filter.atTop, 1 ≤ q.eval lam) →
    (∀ lam, r lam (s.eval lam) (p.eval lam) (q.eval lam) ≤ m.eval lam) →
    ∀ Gd : List Bool, RunsInTime Gd (fun lam => t'.eval lam) →
      (∀ lam z, 0 < algProb GS Gd (unary lam) z →
        ValidPOVMInstance GS (n.eval lam) (s.eval lam) (t.eval lam) (m.eval lam) z) →
      ∀ᶠ lam in Filter.atTop,
        1 - 1 / ((q.eval lam : ℕ) : ℝ) ≤
          avgSuccessPOVM GS L Gd lam (n.eval lam) (s.eval lam) (t.eval lam) (t'.eval lam)
            (p.eval lam) (q.eval lam) (m.eval lam)

end QIndInf.Supplement


