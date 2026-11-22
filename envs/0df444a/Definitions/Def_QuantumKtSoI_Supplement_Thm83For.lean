-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_Thm83For
-- name    : QuantumKtSoI_Supplement_Thm83For
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:39:35.013798+00:00
-- url     : https://prove2.me/theorems/1ac15709-b95f-4fe2-bb4a-cee9bc904a1d
-- title:
--   Theorems A.1, 8.3 and Propositions A.2, 8.4 for a conditional measure $\mu$; pseudorandom generators and exponentially hard one-way functions
-- statement:
--   A **quantum-secure pseudorandom generator** is a family $\mathrm{Gen}_n:\{0,1\}^{\lambda(n)}\to\{0,1\}^{\ell^*(n)}$, with $\lambda,\ell^*$ computable in time polynomial in $n$, $1\le\lambda(n)<\ell^*(n)$ and $\ell^*$ polynomially bounded, computed from $(1^n,s)$ by one deterministic polynomial-time algorithm, such that for every polynomial-time machine $D$ the advantage
--   $$\mathrm{adv}_D(n)=\Big|\Pr_s[D \text{ outputs } 1 \text{ on } \langle1^n,\mathrm{Gen}_n(s)\rangle]-\Pr_w[D \text{ outputs } 1 \text{ on } \langle1^n,w\rangle]\Big|$$
--   is negligible. An **exponentially hard quantum-secure one-way function with linear output length**, with constants $\gamma\in(0,1]$ and an integer $a\ge1$, is a polynomial-time computable family $f_m$ with $|f_m(z)|\le am$ such that every machine that eventually halts within $2^{\gamma m}$ steps on every $\langle1^m,u\rangle$ with $|u|\le am$ inverts $f_m$ on a uniform input with probability less than $2^{-\gamma m}$, for all large $m$.
--
--   For a real-valued conditional measure $\mu$ this module states, with $\mu$ in place of $\mathrm{qKt}$:
--
--   1. **Theorem A.1**: if a classical polynomial-time sampler of pairs in $\{0,1\}^{m(n)}\times\{0,1\}^{m(n)}$ satisfies (26) $\Pr_x[\Pr[y=\varphi_n(x)\mid x]\ge 255/256]\ge\delta_0$ for all large $n$ and (27) $\Pr[\mu(y|x)\le C\log n]=o(1)$ for every $C>0$, then a quantum-secure one-way function exists;
--   2. **Proposition A.2**: a quantum-secure pseudorandom generator gives such a sampler with $\Pr[Y\ne\varphi_n(X)]$ negligible and $\Pr[\mu(Y|X)\le B\log(n+2)]$ negligible for every $B\ge0$, which in particular satisfies (26) and (27);
--   3. **Theorem 8.3**: a quantum-secure one-way function gives a fixed classical sampler $S$ and lengths $N_m=A_0(m+2)^D$ with $\Pr_{S(1^{N_m})}[\mu(Y|X)+\mu(X)-\mu(\langle X,Y\rangle)>C\log(2N_m+2)]\ge1-\varepsilon_C(m)$ for a negligible $\varepsilon_C$, for every $C\ge0$, together with the seed form of $S$, the bound $\Pr_Z[\mu(Y|X)\le\log F_{f_m(Z)}+B\log(m+2)]$ negligible for every $B\ge0$, and decidability of $\{N_m\}$;
--   4. **Proposition 8.4**: an exponentially hard quantum-secure one-way function with linear output length gives $\eta>0$, a sampler and $N_m=(a+1)(m+K)$ with $\Pr[\mu(Y|X)+\mu(X)-\mu(\langle X,Y\rangle)>\eta(|X|+|Y|)]\ge1-2^{-\eta N_m}$ for all large $m$, and hence infinitely many pairs with defect above $\eta(|x|+|y|)$.
--
--   Theorem F.3(e) asserts these for $\mathrm{qKt}^{(c)}$; at $\mu=\mathrm{qKt}$ each is the paper's statement.
--
--   **Formalization Note** Classical samplers are those of the base mission (probabilistic Turing machines with an all-branch polynomial deadline). In (26) the conditional probability is written as a ratio inequality on $x$ of positive probability. "An encoding of $m$ and $f_m(Z)$" is an injective map. Real deadlines are floors.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Theorem A.1, p.131; Proposition A.2 and pseudorandom generators, p.135; Theorem 8.3, p.113; Proposition 8.4 and exponentially hard one-way functions, p.115; Open Problem 2, p.9

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_CodedMachine
import Definitions.Def_QuantumKtSoI_PolySampler
import Definitions.Def_QuantumKtSoI_Supplement_GSampler
import Definitions.Def_QuantumKtSoI_Supplement_PolyInValue
import Definitions.Def_QuantumKtSoI_Supplement_QSOWF
import Definitions.Def_QAdvFew_PoQOracle_Negligible

open Classical

noncomputable section

namespace QuantumKtSoI.Supplement

/-! The sampler results of §8 and Appendix A for a conditional measure `µ` (`µ y x` is `µ(y | x)`,
`µ(y) = µ(y | ε)`; Myrisiotis, *Failure of Symmetry of Information for Quantum Computations*, STOC 2027 submission, held version sha256 6616571c…). With `µ = qKt` each is the paper's statement; Theorem F.3(e) asserts them
with `qKt^{(c)}` in place of `qKt`. -/

/-- A **quantum-secure pseudorandom generator** (p.135): a family
`Gen_n : {0,1}^{λ(n)} → {0,1}^{ℓ*(n)}` with `λ` and `ℓ*` computable in time polynomial in `n`,
`1 ≤ λ(n) < ℓ*(n)` and `ℓ*` polynomially bounded, such that one deterministic classical
polynomial-time algorithm computes `Gen_n(s)` from `(1ⁿ, s)`, and for every machine `D` of
Definition 3.1 that halts within a fixed polynomial in `n + |u|` steps on every branch and every
input `⟨1ⁿ, u⟩` the advantage
`adv_D(n) = |Pr_s[D outputs 1 on ⟨1ⁿ, Gen_n(s)⟩] − Pr_w[D outputs 1 on ⟨1ⁿ, w⟩]|`
is negligible in `n`, `s` and `w` uniform in `{0,1}^{λ(n)}` and `{0,1}^{ℓ*(n)}`.

**Formalization Note** `gen n s` is `Gen_n(s)`; `(1ⁿ, s)` is the pair `⟨1ⁿ, s⟩`; "computable in
time polynomial in `n`" is `PolyInValue`; polynomial time for `Gen` is `c(n+2)^k` steps (the
input length is polynomial in `n`); a distinguisher is the `Adversary` of Definition 8.1 (the
same machine class), read at its all-branch deadline. -/
def QuantumSecurePRG (lam ell : ℕ → ℕ) (gen : ℕ → List Bool → List Bool) : Prop :=
  PolyInValue lam ∧ PolyInValue ell ∧ (∀ n, 1 ≤ lam n ∧ lam n < ell n) ∧
    (∃ c k : ℕ, ∀ n, ell n ≤ c * (n + 2) ^ k) ∧
    (∀ n : ℕ, ∀ s : List Bool, s.length = lam n → (gen n s).length = ell n) ∧
    (∃ F : CodedMachine, F.Valid ∧ F.GateFree ∧ ∃ c k : ℕ, ∀ n : ℕ, ∀ s : List Bool,
      s.length = lam n →
        F.toMachine.HaltsWithin (pair (ones n) s) (c * (n + 2) ^ k) ∧
          F.toMachine.outputProb (pair (ones n) s) (c * (n + 2) ^ k) (gen n s) = 1) ∧
    ∀ D : Adversary, QAdvFew.PoQOracle.Negligible fun n =>
      |(∑ s : Fin (lam n) → Bool, (1 / 2 ^ lam n : ℝ) *
          D.A.toMachine.outputProb (pair (ones n) (gen n (List.ofFn s)))
            (D.c * (n + (gen n (List.ofFn s)).length + 2) ^ D.k) [true]) -
        ∑ w : Fin (ell n) → Bool, (1 / 2 ^ ell n : ℝ) *
          D.A.toMachine.outputProb (pair (ones n) (List.ofFn w))
            (D.c * (n + (List.ofFn w : List Bool).length + 2) ^ D.k) [true]|

/-- An **exponentially hard quantum-secure one-way function with linear output length** (p.115),
with constants `γ ∈ (0, 1]` and an integer `a ≥ 1`: a family `f_m : {0,1}^m → {0,1}*` computed
from `⟨1^m, z⟩` by one deterministic classical polynomial-time algorithm such that
`|f_m(z)| ≤ am` for all `m ≥ 1` and `z ∈ {0,1}^m`, and for every machine `A` of Definition 3.1
that, for all sufficiently large `m`, halts within `2^{γm}` steps on every branch and every input
`⟨1^m, u⟩` with `|u| ≤ am`: for all sufficiently large `m`, the probability that `A`, run on
`⟨1^m, f_m(Z)⟩` for uniform `Z ∈ {0,1}^m`, outputs some `z′ ∈ {0,1}^m` with `f_m(z′) = f_m(Z)` is
less than `2^{−γm}`.

**Formalization Note** The real deadline `2^{γm}` is read as `⌊·⌋` (p.22), and the output of `A` is
read at that deadline. -/
def ExpHardOWF (f : List Bool → List Bool) (γ : ℝ) (a : ℕ) : Prop :=
  0 < γ ∧ γ ≤ 1 ∧ 1 ≤ a ∧
    (∃ F : CodedMachine, F.Valid ∧ F.GateFree ∧ ∃ c k : ℕ, ∀ m : ℕ, ∀ z : List Bool, z.length = m →
      F.toMachine.HaltsWithin (pair (ones m) z) (c * (m + 2) ^ k) ∧
        F.toMachine.outputProb (pair (ones m) z) (c * (m + 2) ^ k) (f z) = 1) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ z : List Bool, z.length = m → (f z).length ≤ a * m) ∧
    ∀ A : CodedMachine, A.Valid →
      (∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ u : List Bool, u.length ≤ a * m →
        A.toMachine.HaltsWithin (pair (ones m) u) ⌊(2 : ℝ) ^ (γ * m)⌋₊) →
      ∃ m₁ : ℕ, ∀ m ≥ m₁,
        (∑ Z : Fin m → Bool, (1 / 2 ^ m : ℝ) *
          ∑ z' ∈ (Finset.univ : Finset (Fin m → Bool)).filter
              (fun z' => f (List.ofFn z') = f (List.ofFn Z)),
            A.toMachine.outputProb (pair (ones m) (f (List.ofFn Z))) ⌊(2 : ℝ) ^ (γ * m)⌋₊
              (List.ofFn z')) < (2 : ℝ) ^ (-(γ * m))

/-- Hypothesis (26) of Theorem A.1 (p.131) for a sampler `S`, a constant `δ₀` and functions
`φ_n`: for all sufficiently large `n`, `Pr_x[Pr[y = φ_n(x) | x] ≥ 255/256] ≥ δ₀`, where `x` is the
first coordinate of `S(1ⁿ)` and the inner probability is over the second coordinate given the
first.

**Formalization Note** `Pr_x[E(x)]` is the sum of `Pr[X = x]` over the `x ∈ {0,1}^{m(n)}` with
`Pr[X = x] > 0` and `E(x)`; `Pr[y = φ_n(x) | x] ≥ 255/256` is
`Pr[X = x, Y = φ_n(x)] ≥ (255/256) Pr[X = x]`. -/
def A1Hyp26 {m : ℕ → ℕ} (S : GSampler m) (δ₀ : ℝ) (φ : ℕ → List Bool → List Bool) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, δ₀ ≤ ∑ x : Fin (m n) → Bool,
    if 0 < S.prob n (fun X _ => X = List.ofFn x) ∧
        (255 / 256 : ℝ) * S.prob n (fun X _ => X = List.ofFn x) ≤
          S.prob n (fun X Y => X = List.ofFn x ∧ Y = φ n (List.ofFn x))
      then S.prob n (fun X _ => X = List.ofFn x) else 0

/-- Hypothesis (27) of Theorem A.1 (p.131) for `µ`: for every constant `C > 0`,
`Pr_{(x,y)∼S(1ⁿ)}[µ(y|x) ≤ C log n] = o(1)` (for every `ε > 0`, eventually at most `ε`). -/
def A1Hyp27 (μ : List Bool → List Bool → ℝ) {m : ℕ → ℕ} (S : GSampler m) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    S.prob n (fun x y => μ y x ≤ C * Real.logb 2 n) ≤ ε

/-- **Theorem A.1** (Almost-determined classical sampling implies one-wayness, p.131) for `µ`: for
every classical polynomial-time sampler `S` with outputs in `{0,1}^{m(n)} × {0,1}^{m(n)}`, `m`
polynomially bounded and polynomial-time computable, if (26) holds for some `δ₀ > 0` and functions
`φ_n : {0,1}^{m(n)} → {0,1}^{m(n)}`, and (27) holds for `µ`, then a quantum-secure classical
one-way function (Definition 8.1) exists. -/
def ThmA1For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ m : ℕ → ℕ, (∃ c k : ℕ, ∀ n, m n ≤ c * (n + 2) ^ k) → PolyInValue m → ∀ S : GSampler m,
    ∀ δ₀ : ℝ, 0 < δ₀ → ∀ φ : ℕ → List Bool → List Bool,
      (∀ n : ℕ, ∀ x : List Bool, x.length = m n → (φ n x).length = m n) →
      A1Hyp26 S δ₀ φ → A1Hyp27 μ S → ∃ f : List Bool → List Bool, QuantumSecureOWF f

/-- **Proposition A.2** (Samplers from pseudorandom generators, p.135) for `µ`: if a quantum-secure
pseudorandom generator exists, then there are a fixed classical polynomial-time sampler `S`,
outputting `(X, Y) ∈ {0,1}^{M(n)} × {0,1}^{M(n)}` on `1ⁿ` for a polynomially bounded,
polynomial-time computable `M`, and functions `φ_n : {0,1}^{M(n)} → {0,1}^{M(n)}` such that
`Pr[Y ≠ φ_n(X)]` is negligible in `n` and, for every real `B ≥ 0`, `Pr[µ(Y|X) ≤ B log(n+2)]` is
negligible in `n`. In particular `S` satisfies the hypotheses (26), (27) of Theorem A.1. -/
def PropA2For (μ : List Bool → List Bool → ℝ) : Prop :=
  (∃ lam ell : ℕ → ℕ, ∃ gen : ℕ → List Bool → List Bool, QuantumSecurePRG lam ell gen) →
  ∃ M : ℕ → ℕ, (∃ c k : ℕ, ∀ n, M n ≤ c * (n + 2) ^ k) ∧ PolyInValue M ∧ ∃ S : GSampler M,
    ∃ φ : ℕ → List Bool → List Bool,
      (∀ n : ℕ, ∀ x : List Bool, x.length = M n → (φ n x).length = M n) ∧
      QAdvFew.PoQOracle.Negligible (fun n => S.prob n fun X Y => Y ≠ φ n X) ∧
      (∀ B : ℝ, 0 ≤ B → QAdvFew.PoQOracle.Negligible fun n =>
        S.prob n fun X Y => μ Y X ≤ B * Real.logb 2 ((n : ℝ) + 2)) ∧
      (∃ δ₀ : ℝ, 0 < δ₀ ∧ A1Hyp26 S δ₀ φ) ∧ A1Hyp27 μ S

/-- **Theorem 8.3** (Classical sampling from quantum-secure one-way functions, p.113) for `µ`: if
`f_m : {0,1}^m → {0,1}*` is a quantum-secure classical one-way function, there are a fixed
classical polynomial-time sampler `S` (`S(1^N)` outputs `(X, Y) ∈ {0,1}^N × {0,1}^N`) and an
increasing polynomial `N_m = A₀(m+2)^D`, `A₀, D ≥ 1` integers, such that
1. for every constant `C ≥ 0` a negligible `ε_C` satisfies
   `Pr_{(X,Y)∼S(1^{N_m})}[µ(Y|X) + µ(X) − µ(⟨X,Y⟩) > C log(2N_m+2)] ≥ 1 − ε_C(m)` for all `m ≥ 1`,
   and `ε_C` is also negligible as a function of `N_m`;
2. `S(1^{N_m})` draws a uniform seed `Z ∈ {0,1}^m` and outputs `Y = Z0^{N_m−m}` and an encoding
   `X` of `m` and `f_m(Z)`;
3. with `F_y = |f_m^{−1}(y)|`, for every constant `B ≥ 0` the probability
   `Pr_Z[µ(Y|X) ≤ log F_{f_m(Z)} + B log(m+2)]` is negligible in `m`;
4. the set of lengths `{N_m}` is decidable in time polynomial in `N`.

**Formalization Note** As in `theorem_8_3`: `S` is a published `PolySampler`; "an encoding of `m`
and `f_m(Z)`" is an injective `Enc(m, y)`; "draws a uniform seed and outputs …" is: for every
`z ∈ {0,1}^m` the output is `(Enc(m, f_m(z)), z0^{N_m−m})` with probability `2^{−m}`; "negligible as
a function of `N_m`" is: for every `c > 0`, eventually `ε_C(m) ≤ N_m^{−c}`; decidability of
`{N_m}` is by a deterministic machine on input `b(N)` within `c(N+2)^k` steps. -/
def Thm83For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ f : List Bool → List Bool, QuantumSecureOWF f →
    ∃ S : PolySampler, ∃ A₀ D : ℕ, 1 ≤ A₀ ∧ 1 ≤ D ∧
      (∀ C : ℝ, 0 ≤ C → ∃ ε : ℕ → ℝ, QAdvFew.PoQOracle.Negligible ε ∧
        (∀ m : ℕ, 1 ≤ m → 1 - ε m ≤
          S.prob (A₀ * (m + 2) ^ D) fun X Y =>
            C * Real.logb 2 (2 * ((A₀ * (m + 2) ^ D : ℕ) : ℝ) + 2) <
              μ Y X + μ X [] - μ (pair X Y) []) ∧
        ∀ c : ℝ, 0 < c → ∃ m₀ : ℕ, ∀ m ≥ m₀, ε m ≤ ((A₀ * (m + 2) ^ D : ℕ) : ℝ) ^ (-c)) ∧
      (∃ Enc : ℕ → List Bool → List Bool,
        (∀ m m' : ℕ, ∀ y y' : List Bool, Enc m y = Enc m' y' → m = m' ∧ y = y') ∧
        (∀ m : ℕ, 1 ≤ m → ∀ z : Fin m → Bool,
          S.prob (A₀ * (m + 2) ^ D) (fun X Y => X = Enc m (f (List.ofFn z)) ∧
            Y = List.ofFn z ++ List.replicate (A₀ * (m + 2) ^ D - m) false) = 1 / 2 ^ m) ∧
        ∀ B : ℝ, 0 ≤ B → QAdvFew.PoQOracle.Negligible fun m =>
          ((Finset.univ.filter fun z : Fin m → Bool =>
              μ (List.ofFn z ++ List.replicate (A₀ * (m + 2) ^ D - m) false)
                  (Enc m (f (List.ofFn z))) ≤
                Real.logb 2 ((Finset.univ.filter fun z' : Fin m → Bool =>
                    f (List.ofFn z') = f (List.ofFn z)).card : ℝ) +
                  B * Real.logb 2 ((m : ℝ) + 2)).card : ℝ) / 2 ^ m) ∧
      ∃ F : CodedMachine, F.Valid ∧ F.GateFree ∧ ∃ c k : ℕ, ∀ N : ℕ,
        F.toMachine.HaltsWithin (bin N) (c * (N + 2) ^ k) ∧
          F.toMachine.outputProb (bin N) (c * (N + 2) ^ k)
            [decide (∃ m : ℕ, 1 ≤ m ∧ N = A₀ * (m + 2) ^ D)] = 1

/-- **Proposition 8.4** (Linear error from exponentially hard one-way functions, p.115) for `µ`:
if `f` is an exponentially hard quantum-secure one-way function with linear output length, with
output-length constant `a`, then there are a constant `η > 0`, a fixed classical polynomial-time
sampler `S` and a constant `K` such that, with the strictly increasing `N_m = (a+1)(m+K)`,
`S(1^{N_m})` outputs a pair `(X, Y) ∈ {0,1}^{N_m} × {0,1}^{N_m}` with
`Pr[µ(Y|X) + µ(X) − µ(⟨X,Y⟩) > η(|X|+|Y|)] ≥ 1 − 2^{−ηN_m}` for all sufficiently large `m`. In
particular the question of Open Problem 2 (p.9) then has a positive answer for `µ`: for some
`η > 0`, infinitely many pairs `(x, y)` satisfy `µ(x) + µ(y|x) − µ(⟨x,y⟩) > η(|x|+|y|)`.

**Formalization Note** `S` is a published `PolySampler` (output length `2N` on `1^N`); `K` is a
natural number. -/
def Prop84For (μ : List Bool → List Bool → ℝ) : Prop :=
  ∀ (f : List Bool → List Bool) (γ : ℝ) (a : ℕ), ExpHardOWF f γ a →
    (∃ η : ℝ, 0 < η ∧ ∃ S : PolySampler, ∃ K m₀ : ℕ, ∀ m ≥ m₀,
      1 - (2 : ℝ) ^ (-(η * (((a + 1) * (m + K) : ℕ) : ℝ))) ≤
        S.prob ((a + 1) * (m + K)) fun X Y =>
          η * ((X.length : ℝ) + Y.length) < μ Y X + μ X [] - μ (pair X Y) []) ∧
    ∃ η : ℝ, 0 < η ∧ {p : List Bool × List Bool |
      η * ((p.1.length : ℝ) + p.2.length) < μ p.1 [] + μ p.2 p.1 - μ (pair p.1 p.2) []}.Infinite

end QuantumKtSoI.Supplement


