-- Prove2me | Definitions.Def_QIndInf_Supplement_SolvesAvg
-- name    : QIndInf_Supplement_SolvesAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:24:25.981366+00:00
-- url     : https://prove2.me/theorems/25ac3995-06bb-4f28-9078-0fa2ef4b64cc
-- title:
--   Definition 4.3 — average-case universal quantum inductive inference
-- statement:
--   Let $L$ be a quantum algorithm. At round $i$ it receives the classical input $\mathsf{param}_\lambda=(1^\lambda,1^{n(\lambda)},1^{s(\lambda)},1^{t(\lambda)},1^{t'(\lambda)},1^{p(\lambda)},1^{q(\lambda)})$, the history $h_{<i}=(\mathcal I_1,x_1,\dots,\mathcal I_{i-1},x_{i-1})$ (instrument descriptions and outcomes) and the description of the next instrument $\mathcal I_i$, together with the quantum state $\rho^T_{R_1\dots R_{i-1}|h_{<i}}$; it outputs a state on $(R_1,\dots,R_i,X_i)$.
--
--   $L$ **solves average-case universal quantum inductive inference with round complexity** $r$ if for all polynomials $m,n,s,t,t',p,q$ with $m(\lambda)\ge r(\lambda,s(\lambda),p(\lambda),q(\lambda))$ and every $t'(\lambda)$-time algorithm $\mathcal G$ that on $1^\lambda$ outputs a program $T$ with $|T|\le s(\lambda)$ whose $t(\lambda)$-step run writes a circuit description of $\rho^T_{R_1\dots R_m}\in\mathcal C_{n(\lambda),m}[s(\lambda),t(\lambda)]$ and instruments $\mathcal I_1,\dots,\mathcal I_{m(\lambda)}$ ($\mathcal I_i$ on $R_i$), for all sufficiently large $\lambda$
--   $$\Pr_{\substack{i\leftarrow[m],\ (T,\mathcal I)\leftarrow\mathcal G(1^\lambda)\\ x_{<i}\leftarrow D^{\mathcal I,\rho^T}_{<i}}}\Big[\mathrm{TD}\big(L(\mathsf{param}_\lambda,h_{<i},\mathcal I_i,\rho^T_{R_1\dots R_{i-1}|h_{<i}}),\ \tau^T_{R_1\dots R_i|h_{<i}}\big)\le\frac1{p(\lambda)}\Big]\ \ge\ 1-\frac1{q(\lambda)} .$$
--
--   Here $D^{\mathcal I,\rho}_{<i}$, $\rho_{<i|h_{<i}}$ and the target $\tau_{\le i|h_{<i}}$ are those of Eqs. (52), (53) and (55), and $\mathrm{TD}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$. This is the average-case task whose hardness Theorem 4.4 proves.
--
--   **Formalization Note** Polynomials are `Polynomial ℕ`, with $m(\lambda),p(\lambda),q(\lambda)\ge1$ for all sufficiently large $\lambda$. The syntax of $\mathcal G$ is required of every output of positive probability. A round counts as a success only if $L$ writes a circuit with the right numbers of input and output wires. $L$ gets neither $m$, nor $T$, nor later instruments. The base mission's `outcomeProb`, `condPast` and `target` are reused.
-- source:
--   Hiroka, Hsieh, Shirakawa, Universal Inductive Inference of Quantum States, arXiv:2609.36912 (PDF of 2026-11-02, sha256 ac6387756651cc50c671f36acf1ef987db0df0c463581cd948250204441f6925), §4.3, Definition 4.3, Eq. (77), pp.21–22; Eqs. (51)–(55), pp.18–19

import Mathlib
import Definitions.Def_QIndInf_Supplement_instrOf
import Definitions.Def_QIndInf_successProb
import Definitions.Def_QiOPoQ_pair

set_option autoImplicit false

namespace QIndInf.Supplement

open QAlgorithms QAlgorithms.Complexity QAlgorithms.CopyMeasurements QiOPoQ QIndInf

/-- `param_λ = (1^λ, 1^{n(λ)}, 1^{s(λ)}, 1^{t(λ)}, 1^{t′(λ)}, 1^{p(λ)}, 1^{q(λ)})` as one string
(Definitions 4.3 and 5.4). -/
def paramStr (lam n s t t' p q : ℕ) : List Bool :=
  QAdvFew.PoQOracle.tup [unary lam, unary n, unary s, unary t, unary t', unary p, unary q]

/-- `(T, I₁, …, I_M)` decoded from an output `z` of the instance generator: the program `T` and
the instrument (or POVM) descriptions. -/
noncomputable def instParts (z : List Bool) : Option (List Bool × List (List Bool)) :=
  match untuple z with
  | some (T :: ds) => some (T, ds)
  | _ => none

/-- **A valid instance of Definition 4.3**: `z = (T, I₁, …, I_m)` with `|T| ≤ s`, `T^t` writing
a circuit description (of the source `ρ^T ∈ C_{n,m}[s,t]`), and `m` descriptions of circuits
implementing instruments on one `n`-qubit register each. -/
def ValidInstance (G : GateSet) (n s t m : ℕ) (z : List Bool) : Prop :=
  ∃ T ds, instParts z = some (T, ds) ∧ T.length ≤ s ∧ (srcCirc G T t).isSome ∧ ds.length = m ∧
    ∀ d ∈ ds, ValidInstrDesc G n d

/-- The history string `h<i = (I₁, x₁, …, I_{i−1}, x_{i−1})`: descriptions and outcome strings. -/
def histStr {j : ℕ} (d : Fin j → List Bool) (xs : Fin j → List Bool) : List Bool :=
  QAdvFew.PoQOracle.tup (List.flatten (List.ofFn fun l => [d l, xs l]))

/-- **The learner's output** `L(param, h<i, I_i, ρ_{<i|h<i})`: the channel of the QPT algorithm `L`
on the classical input `inp`, from the `j·n` qubits of `R₁ … R_j` to the `j·n + n + K` qubits of
`(R₁ … R_j, R_{j+1}, X_{j+1})` (`K` outcome bits of the next instrument), read on the index
`Regs n j × (Reg n × Fin (2^K))` of the base mission's `target`. -/
noncomputable def learnerOut (G : GateSet) (L inp : List Bool) (n j K : ℕ)
    (ρ : Matrix (Regs n j) (Regs n j) ℂ) :
    Matrix (Regs n j × (Reg n × Fin (2 ^ K))) (Regs n j × (Reg n × Fin (2 ^ K))) ℂ :=
  let e : (Fin (j * n + (n + K)) → Bool) ≃ Regs n j × (Reg n × Fin (2 ^ K)) :=
    (splitEquiv (j * n) (n + K)).trans (Equiv.prodCongr (regsEquiv n j)
      ((splitEquiv n K).trans (Equiv.prodCongr (bitsEquiv n) (bitsEquiv K))))
  Matrix.reindex e e (algChan G L inp (j * n) (j * n + (n + K))
    (Matrix.reindex (regsEquiv n j).symm (regsEquiv n j).symm ρ))

/-- The algorithm `A` on the classical input `x` writes a circuit with `a` input and `b` output
wires (a well-formed quantum output). -/
def OutputsOn (G : GateSet) (A x : List Bool) (a b : ℕ) : Prop :=
  ∃ C : Circ G, algCirc G A x = some C ∧ C.nin = a ∧ C.out.length = b

open Classical in
/-- **Success probability on one instance** (the event of Eq. (77) for fixed `(T, I)`):
`Pr_{i ← [m], x<i ← D^{I,ρ}_{<i}} [TD(L(param, h<i, I_i, ρ_{<i|h<i}), τ_{≤i|h<i}) ≤ 1/p]`, with the
base mission's `outcomeProb` (Eq. (52)), `condPast` (Eq. (53)) and `target` (Eq. (55)) for the
source `σ` and the instruments described by `ds`; `TD = ½·WildeQIT.traceDist`. A round counts as a
success only if `L` writes a circuit from the `j·n` input qubits to the `j·n + n + K` output qubits
(`OutputsOn`), so its output is a state on `(R₁ … R_i, X_i)`. -/
noncomputable def instSuccess (G : GateSet) (L prm : List Bool) (n m p : ℕ)
    (σ : (j : ℕ) → Matrix (Regs n j) (Regs n j) ℂ) (ds : List (List Bool)) : ℝ :=
  let kx : Fin m → ℕ := fun j => (instrOf G n (ds.getD j.val [])).1
  let k : Fin m → ℕ := fun j => 2 ^ kx j
  let I : (j : Fin m) → QuantumInstrument (Reg n) (Fin (k j)) :=
    fun j => (instrOf G n (ds.getD j.val [])).2
  (1 / (m : ℝ)) * ∑ j : Fin m, ∑ x : (l : Fin j.val) → Fin (prefK k j l.castSucc),
    outcomeProb σ (pastInstr (prefI I j)) x *
      (let inp := QAdvFew.PoQOracle.tup [prm,
          histStr (fun l => ds.getD l.val [])
            (fun l => outcomeStr (k := kx (Fin.castLE (Nat.succ_le_of_lt j.isLt) l.castSucc)) (x l)),
          ds.getD j.val []]
       let K := kx (Fin.castLE (Nat.succ_le_of_lt j.isLt) (Fin.last j.val))
       if OutputsOn G L inp (j.val * n) (j.val * n + (n + K)) ∧
          (1 / 2 : ℝ) * WildeQIT.traceDist
            (learnerOut G L inp n j.val K (condPast σ (pastInstr (prefI I j)) x))
            (target σ (prefI I j) x) ≤ 1 / (p : ℝ)
        then 1 else 0)

/-- **Average success at security parameter `λ`** (left side of Eq. (77)): the probability over
`(T, I) ← G(1^λ)`, `i ← [m]` and `x<i ← D^{I,ρ^T}_{<i}`. -/
noncomputable def avgSuccess (G : GateSet) (L Gd : List Bool) (lam n s t t' p q m : ℕ) : ℝ :=
  ∑' z : List Bool, algProb G Gd (unary lam) z *
    (match instParts z with
      | some (T, ds) => instSuccess G L (paramStr lam n s t t' p q) n m p (srcFamily G n t T) ds
      | none => 0)

/-- **Definition 4.3 (average-case universal quantum inductive inference).** The algorithm `L`
solves average-case universal quantum inductive inference with round complexity `r` if for all
polynomials `m, n, s, t, t′, p, q` with `m(λ) ≥ r(λ, s(λ), p(λ), q(λ))` and every `t′(λ)`-time
algorithm `G` that on `1^λ` outputs a program `T` with `|T| ≤ s(λ)` whose `t(λ)`-step run writes a
circuit description of `ρ^T`, together with instruments `I₁, …, I_{m(λ)}` (`I_i` on `R_i`), for all
sufficiently large `λ`:
`Pr_{i, (T,I) ← G(1^λ), x<i} [TD(L(param_λ, h<i, I_i, ρ^T_{<i|h<i}), τ^T_{≤i|h<i}) ≤ 1/p(λ)] ≥ 1 − 1/q(λ)`.

arXiv:2609.36912 (PDF of 2026-11-02), §4.3, Definition 4.3, Eq. (77), pp.21–22.

**Formalization Note.**
* `L` is a quantum algorithm (`algChan`) over the gate set `GS`; the definition is used with
  `IsQPT L`. Its classical input is exactly `(param_λ, h<i, I_i)` (descriptions); its quantum input
  is `ρ^T_{<i|h<i}`; it gets neither `m`, nor `T`, nor later instruments.
* `G` is a quantum algorithm with classical output that runs in time `t′(λ)` (`RunsInTime`); the
  syntax of its outputs is required of every output of positive probability (`ValidInstance`).
* Polynomials are `Polynomial ℕ`; `m(λ), p(λ), q(λ) ≥ 1` for all sufficiently large `λ`
  (`i ← [m]`, `ε = 1/p`, `δ = 1/q`; the success condition is only asked for large `λ`, so e.g.
  `p(λ) = λ` is admitted, as in the paper).
* `r` is any function `ℕ⁴ → ℕ` here; Theorem 4.4 takes it polynomial. -/
def SolvesAvg (GS : GateSet) (L : List Bool) (r : ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (m n s t t' p q : Polynomial ℕ),
    (∀ᶠ lam in Filter.atTop, 1 ≤ m.eval lam) → (∀ᶠ lam in Filter.atTop, 1 ≤ p.eval lam) →
    (∀ᶠ lam in Filter.atTop, 1 ≤ q.eval lam) →
    (∀ lam, r lam (s.eval lam) (p.eval lam) (q.eval lam) ≤ m.eval lam) →
    ∀ Gd : List Bool, RunsInTime Gd (fun lam => t'.eval lam) →
      (∀ lam z, 0 < algProb GS Gd (unary lam) z →
        ValidInstance GS (n.eval lam) (s.eval lam) (t.eval lam) (m.eval lam) z) →
      ∀ᶠ lam in Filter.atTop,
        1 - 1 / ((q.eval lam : ℕ) : ℝ) ≤
          avgSuccess GS L Gd lam (n.eval lam) (s.eval lam) (t.eval lam) (t'.eval lam)
            (p.eval lam) (q.eval lam) (m.eval lam)

end QIndInf.Supplement


