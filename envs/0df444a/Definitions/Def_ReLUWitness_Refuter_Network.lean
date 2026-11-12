-- Prove2me | Definitions.Def_ReLUWitness_Refuter_Network
-- name    : ReLUWitness_Refuter_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:53:01.725436+00:00
-- url     : https://prove2.me/theorems/fea2d468-a193-4e57-be8d-85824f572f63
-- title:
--   The network record and Net(N,n); the fixed-depth evaluator Eval_K and Err_K; ValGood_q by the Lemma 8.4 graphs; the cutoff p
-- statement:
--   **The record.** A network with input dimension $d_0=n$, hidden depth $k$, positive widths $d_1,\dots,d_k$ and scalar output $d_{k+1}=1$ is coded by the exact record
--   $$N=(\mathrm{Meta},\mathrm{Par}),\qquad \mathrm{Meta}=(\mathrm{Un}(n),\mathrm{Dim},\mathrm{Un}(k),\mathrm{Un}(q_{\mathrm{hid}}),\mathrm{Un}(M)),$$
--   with $\mathrm{Dim}=(\mathrm{Un}(d_1),\dots,\mathrm{Un}(d_{k+1}))$, $q_{\mathrm{hid}}=\sum_{j=1}^k d_j$, $p_j=d_jd_{j-1}+d_j$, $M=\sum_{j=1}^{k+1}p_j$ and offsets $O_1=0$, $O_{j+1}=O_j+p_j$. $\mathrm{Par}$ is an exact tuple of $M$ rational pairs: entry $O_j+id_{j-1}+t+1$ is the weight $W_j[i,t]$ and entry $O_j+d_jd_{j-1}+i+1$ the bias $\eta_j[i]$ (zero-based $i,t$). $\mathrm{Net}(N,n)$ checks all of this: the exact two-entry record and five-entry $\mathrm{Meta}$, every unary field, $n\ge1$, positive dimensions, $d_{k+1}=1$, the equations for $q_{\mathrm{hid}}$ and $M$ (each sum is the number of bits, by $\mathrm{numones}$, of the exact set of pairs it counts), every entry a valid rational pair, and no unused bits. The depth condition is $k\le K$.
--
--   **The guarded evaluator $\mathrm{Eval}_K$ (p. 51).** On $N,x$ it returns nothing unless $\mathrm{Net}(N,n)$ holds for the recorded $n$, $x$ is a valid rational $n$-vector and $k\le K$. Otherwise, with parameters $u_\lambda/b_\lambda$ and inputs $x_i=p_i/\varepsilon_i$, put
--   $$D=\prod_\lambda b_\lambda,\quad E=\prod_i\varepsilon_i,\quad U_\lambda=u_\lambda\prod_{\mu\ne\lambda}b_\mu,\quad A_{0i}=p_i\prod_{h\ne i}\varepsilon_h,$$
--   $$\bar A_{ji}=\sum_{h=1}^{d_{j-1}}U_{jih}A_{j-1,h}+U_{ji,\mathrm{bias}}D^{j-1}E,$$
--   $A_{ji}=\max(0,\bar A_{ji})$ at hidden layers and $A_{k+1,1}=\bar A_{k+1,1}$, and return the exact pair $(A_{k+1,1},D^{k+1}E)$. Products are interval products of exact arrays (an excluded factor replaced by one), and a signed sum is the difference of the iterated sums of the nonnegative and the negative magnitudes.
--
--   **$\mathrm{Err}_K(N,n,x)$** holds when $x$ is a valid rational $n$-vector and $\mathrm{Eval}_K(N,x)$ is nonempty with a value different, under cross-product comparison, from $\mathrm{MAX}_n(x)$; a failed guard is no error.
--
--   **$\mathrm{ValGood}_q(N,n)$ (Lemma 8.4's graphs, pp. 50-51).** Fix the prime $q$ and put $m=|N|$. For an entry $(u,v)$ let $\nu_v$ be the greatest $t\le m$ for which the remainder of the magnitude of $v$ divided by $q^t$ is zero, with $q^t$ the interval product of $t$ copies of $q$. Let $\nu_u$ be the same for $u$, with $\nu_u=m$ when $u=0$. The final flag is $f_m=[\nu_u<\nu_v\wedge m>\nu_u]$. An invalid entry, or one with a component longer than $m$, gets the failed state. $\mathrm{ValGood}_q(N,n)$ is $\mathrm{Net}(N,n)$ together with flag zero at every nonbias (weight) entry; bias denominators are unrestricted.
--
--   **The cutoff.** $p(m)=p_0(m)+2^{100}(m+2)^{40}$ for a polynomial $p_0$ with nonnegative integer coefficients.
--
--   **Formalization Note.** Each predicate is written as its meaning in an arbitrary model (a transcription of the paper's bounded formula). The auxiliary exact arrays (denominator lists, excluded-entry lists, layer products and sums, layer values, the sets counted for $q_{\mathrm{hid}}$, $M$ and $O_j$, the copies of $q$) appear as existentially quantified strings with exactly the specified bits. $\Sigma^B_0$ comprehension provides them, and extensionality makes them unique, so the existential and universal readings coincide in every model of $T$. The external depth $K$ enters through a case split on the actual depth $k=k_0\le K$ and a recursion over the $k_0+1$ affine layers.
-- source:
--   Myrisiotis, A Witnessing Duality for ReLU Network Depth, arXiv:2610.38281v1, pp. 19-21, §2.3 (record, Net, Depth, p); pp. 50-52, Lemma 8.4's proof (normalization graph), Eval_K and Err_K

import Mathlib
import Definitions.Def_ReLUWitness_Refuter_Codes

open scoped Classical

namespace ReLUWitness.Refuter

/-! The fixed network record and `Net(N,n)` (§2.3, pp. 19-20), the fixed-depth guarded
evaluator `Eval_K` and `Err_K` (pp. 51-52), the value-based denominator promise `ValGood_q`
evaluated by the normalization graphs of Lemma 8.4 (pp. 50-51), and the common cutoff
`p(m) = p₀(m) + 2^100 (m+2)^40` (p. 21) (Myrisiotis, arXiv:2610.38281v1), read in an
arbitrary two-sorted structure. Neuron and matrix indices of the record are zero-based;
tuple entries start at row one. -/

noncomputable section

namespace Structure

variable (M : Structure)

/-! ### The fixed network record `N = (Meta, Par)`, `Meta = (Un(n), Dim, Un(k), Un(q_hid), Un(M))` -/

def metaR (N : M.S) : M.S := M.row M.one N
def parR (N : M.S) : M.S := M.row (M.numeral 2) N
/-- Entry `c` (`1 ≤ c ≤ 5`) of `Meta`. -/
def metaF (N : M.S) (c : ℕ) : M.S := M.row (M.numeral c) (M.metaR N)
/-- Recorded input dimension `n`. -/
def inDim (N : M.S) : M.N := M.len (M.metaF N 1)
/-- The dimension tuple `Dim = (Un(d_1), …, Un(d_{k+1}))`. -/
def dimT (N : M.S) : M.S := M.metaF N 2
/-- Recorded hidden depth `k`. -/
def depth (N : M.S) : M.N := M.len (M.metaF N 3)
/-- Recorded hidden-neuron count `q_hid`. -/
def qhid (N : M.S) : M.N := M.len (M.metaF N 4)
/-- Recorded parameter count `M`. -/
def parCnt (N : M.S) : M.N := M.len (M.metaF N 5)
/-- `d_j`: the input dimension `n` at `j = 0`, the `j`-th entry of `Dim` otherwise. -/
def dimAt (N : M.S) (n j : M.N) : M.N :=
  if j = M.zero then n else M.len (M.row j (M.dimT N))
/-- Entry `λ` of `Par` (a rational pair). -/
def entry (N : M.S) (l : M.N) : M.S := M.row l (M.parR N)

/-- `Net(N,n)`: complete validity of the fixed record with input dimension `n`: the exact
two-entry record and five-entry `Meta`, every unary field, `d_0 = n ≥ 1`, all dimensions
positive, `d_{k+1} = 1`, `q_hid = Σ_{1≤j≤k} d_j` and `M = Σ_{1≤j≤k+1} (d_j d_{j-1} + d_j)`
(both sums by counting the bits of the exact sets below), `Par` an exact tuple with `M`
entries, every entry a valid rational pair, and no unused bits. -/
def Net (N : M.S) (n : M.N) : Prop :=
  M.IsTuple N (M.numeral 2) ∧ M.IsTuple (M.metaR N) (M.numeral 5) ∧
  M.IsUn (M.metaF N 1) n ∧ M.le M.one n ∧
  M.IsUn (M.metaF N 3) (M.depth N) ∧ M.IsUn (M.metaF N 4) (M.qhid N) ∧
  M.IsUn (M.metaF N 5) (M.parCnt N) ∧
  M.IsTuple (M.dimT N) (M.add (M.depth N) M.one) ∧
  (∀ j, M.le M.one j → M.le j (M.add (M.depth N) M.one) →
    M.IsUn (M.row j (M.dimT N)) (M.dimAt N n j) ∧ M.le M.one (M.dimAt N n j)) ∧
  M.dimAt N n (M.add (M.depth N) M.one) = M.one ∧
  (∃ H : M.S, M.IsSet H (fun z => ∃ j i, M.le M.one j ∧ M.le j (M.depth N) ∧
      M.lt i (M.dimAt N n j) ∧ z = M.pair j i) ∧
    M.qhid N = M.numones (M.len H) H) ∧
  (∃ W : M.S, M.IsSet W (fun z => ∃ j i t, M.le j (M.depth N) ∧
      M.lt i (M.dimAt N n (M.add j M.one)) ∧ M.le t (M.dimAt N n j) ∧
      z = M.pair (M.add j M.one) (M.pair i t)) ∧
    M.parCnt N = M.numones (M.len W) W) ∧
  M.IsTuple (M.parR N) (M.parCnt N) ∧
  ∀ l, M.le M.one l → M.le l (M.parCnt N) → M.ValidPair (M.entry N l)

/-! ### The guarded fixed-depth evaluator `Eval_K` (p. 51) -/

/-- Offsets `O_1 = 0`, `O_{j+1} = O_j + d_j d_{j-1} + d_j` for an external layer index. -/
def offE (N : M.S) (n : M.N) : ℕ → M.N
  | 0 => M.zero
  | 1 => M.zero
  | j + 2 => M.add (offE N n (j + 1))
      (M.add (M.mul (M.dimAt N n (M.numeral (j + 1))) (M.dimAt N n (M.numeral j)))
        (M.dimAt N n (M.numeral (j + 1))))

/-- `Ā_{ji}` for zero-based neuron `i'` of layer `j`, from the signed sums `Σ_h U_{jih} A_{j-1,h}`
(split into nonnegative and negative parts `Ps`, `Ng`) and the bias term
`U_{ji,bias} D^{j-1} E`. -/
def abar (N : M.S) (n : M.N) (D E : M.S) (U : M.N → M.S) (j : ℕ) (Ps Ng : M.S) (i' : M.N) : M.S :=
  M.sadd
    (M.ssubU (M.isum (M.dimAt N n (M.numeral (j - 1))) (M.row (M.add i' M.one) Ps))
             (M.isum (M.dimAt N n (M.numeral (j - 1))) (M.row (M.add i' M.one) Ng)))
    (M.smul (U (M.add (M.add (M.offE N n j)
        (M.mul (M.dimAt N n (M.numeral j)) (M.dimAt N n (M.numeral (j - 1))))) (M.add i' M.one)))
      (M.smul (M.spow D (j - 1)) E))

/-- Affine layer `j ≥ 1` (external) of `Eval_K`: `cur` is the exact array whose row `i`
(one-based) is `A_{ji} = max(0, Ā_{ji})` (hidden layer) or `Ā_{ji}` (output layer), where
`Ā_{ji} = Σ_{h=1}^{d_{j-1}} U_{jih} A_{j-1,h} + U_{ji,bias} D^{j-1} E`, `U_λ` the cleared
parameter of record entry `λ` (weight `W_j[i-1,h-1]` at `λ = O_j + (i-1) d_{j-1} + h`,
bias `η_j[i-1]` at `λ = O_j + d_j d_{j-1} + i`) and `prev h = A_{j-1,h}`. -/
def LayerStep (N : M.S) (n : M.N) (D E : M.S) (U : M.N → M.S) (j : ℕ) (hidden : Bool)
    (prev : M.N → M.S) (cur : M.S) : Prop :=
  ∃ Pr : M.S, M.IsSet Pr (fun z => ∃ i' h' b,
      M.lt i' (M.dimAt N n (M.numeral j)) ∧ M.lt h' (M.dimAt N n (M.numeral (j - 1))) ∧
      M.mem b (M.smul (U (M.add (M.add (M.offE N n j)
          (M.mul i' (M.dimAt N n (M.numeral (j - 1))))) (M.add h' M.one)))
        (prev (M.add h' M.one))) ∧
      z = M.pair (M.add i' M.one) (M.pair h' b)) ∧
  ∃ Ps : M.S, M.IsSet Ps (fun z => ∃ i' h' b,
      M.lt i' (M.dimAt N n (M.numeral j)) ∧ M.lt h' (M.dimAt N n (M.numeral (j - 1))) ∧
      ¬ M.Neg (M.row h' (M.row (M.add i' M.one) Pr)) ∧
      M.mem b (M.mag (M.row h' (M.row (M.add i' M.one) Pr))) ∧
      z = M.pair (M.add i' M.one) (M.pair h' b)) ∧
  ∃ Ng : M.S, M.IsSet Ng (fun z => ∃ i' h' b,
      M.lt i' (M.dimAt N n (M.numeral j)) ∧ M.lt h' (M.dimAt N n (M.numeral (j - 1))) ∧
      M.Neg (M.row h' (M.row (M.add i' M.one) Pr)) ∧
      M.mem b (M.mag (M.row h' (M.row (M.add i' M.one) Pr))) ∧
      z = M.pair (M.add i' M.one) (M.pair h' b)) ∧
  M.IsSet cur (fun z => ∃ i' b, M.lt i' (M.dimAt N n (M.numeral j)) ∧
      M.mem b (if hidden then M.smax0 (M.abar N n D E U j Ps Ng i') else M.abar N n D E U j Ps Ng i') ∧
      z = M.pair (M.add i' M.one) b)

/-- Layers `j, …, j+r` (the last one the output layer) starting from the values `prev` of
layer `j-1`; `outA` is the output numerator `A_{k+1,1}`. -/
def Layers (N : M.S) (n : M.N) (D E : M.S) (U : M.N → M.S) :
    ℕ → ℕ → (M.N → M.S) → M.S → Prop
  | j, 0, prev, outA => ∃ cur : M.S, M.LayerStep N n D E U j false prev cur ∧ outA = M.row M.one cur
  | j, r + 1, prev, outA => ∃ cur : M.S, M.LayerStep N n D E U j true prev cur ∧
      Layers N n D E U (j + 1) r (fun h => M.row h cur) outA

/-- `out` is the output of the guarded evaluator `Eval_K(N,x)`: both codes are valid
(`Net` at the recorded input dimension, `x` a valid rational vector of that dimension), the
depth `k` is at most `K`, and `out` is the exact pair `(A_{k+1,1}, B_{k+1})`, with
`D` the product of all parameter denominators (biases included), `E` the product of the input
denominators, `U_λ = u_λ ∏_{μ≠λ} b_μ`, `A_{0i} = p_i ∏_{h≠i} ε_h`, `B_j = D^j E`; products are
interval products of exact arrays, an excluded factor replaced by one. -/
def EvalOut (K : ℕ) (N x out : M.S) : Prop :=
  M.Net N (M.inDim N) ∧ M.ValidVec x (M.inDim N) ∧ M.le (M.depth N) (M.numeral K) ∧
  ∃ k₀ : ℕ, k₀ ≤ K ∧ M.depth N = M.numeral k₀ ∧
  ∃ DA : M.S, M.IsSet DA (fun z => ∃ a i, M.lt a (M.parCnt N) ∧
      M.mem i (M.mag (M.qden (M.entry N (M.add a M.one)))) ∧ z = M.pair a i) ∧
  ∃ XA : M.S, M.IsSet XA (fun z => ∃ l a i, M.le M.one l ∧ M.le l (M.parCnt N) ∧
      M.lt a (M.parCnt N) ∧
      ((M.add a M.one ≠ l ∧ M.mem i (M.mag (M.qden (M.entry N (M.add a M.one))))) ∨
        (M.add a M.one = l ∧ i = M.zero)) ∧
      z = M.pair l (M.pair a i)) ∧
  ∃ IA : M.S, M.IsSet IA (fun z => ∃ a i, M.lt a (M.inDim N) ∧
      M.mem i (M.mag (M.qden (M.row (M.add a M.one) x))) ∧ z = M.pair a i) ∧
  ∃ IX : M.S, M.IsSet IX (fun z => ∃ l a i, M.le M.one l ∧ M.le l (M.inDim N) ∧
      M.lt a (M.inDim N) ∧
      ((M.add a M.one ≠ l ∧ M.mem i (M.mag (M.qden (M.row (M.add a M.one) x)))) ∨
        (M.add a M.one = l ∧ i = M.zero)) ∧
      z = M.pair l (M.pair a i)) ∧
  ∃ outA : M.S,
    M.Layers N (M.inDim N)
      (M.mkS False (M.imul M.zero (M.parCnt N) DA))
      (M.mkS False (M.imul M.zero (M.inDim N) IA))
      (fun l => M.smul (M.qnum (M.entry N l))
        (M.mkS False (M.imul M.zero (M.parCnt N) (M.row l XA))))
      1 k₀
      (fun h => M.smul (M.qnum (M.row h x))
        (M.mkS False (M.imul M.zero (M.inDim N) (M.row h IX))))
      outA ∧
    M.IsSet out (fun z => ∃ i,
      (M.mem i outA ∧ z = M.pair M.one i) ∨
      (M.mem i (M.smul (M.spow (M.mkS False (M.imul M.zero (M.parCnt N) DA)) (k₀ + 1))
          (M.mkS False (M.imul M.zero (M.inDim N) IA))) ∧ z = M.pair (M.numeral 2) i))

/-- `Err_K(N,n,x)`: `x` is a valid rational `n`-vector, and the guarded evaluator `Eval_K` at
`N, x` returns a nonempty output whose rational value differs, under cross-product
comparison, from `MAX_n(x)` (the first maximal coordinate). A failed guard is no error. -/
def ErrK (K : ℕ) (N : M.S) (n : M.N) (x : M.S) : Prop :=
  M.ValidVec x n ∧ ∃ out : M.S, M.EvalOut K N x out ∧ M.NonEmpty out ∧
    ∃ a, M.IsFirstMax x n a ∧ ¬ M.qeq out (M.row a x)

/-! ### `ValGood_q` by the normalization graphs of Lemma 8.4 (pp. 50-51) -/

/-- Binary digits of the external prime `q`. -/
def qBits (q : ℕ) : Finset ℕ := (Finset.range (q + 1)).filter (fun i => q.testBit i)

/-- `t = ν_w`: the greatest `t ≤ m` whose division remainder of the magnitude of `w` by `q^t`
is zero, where `q^t` is the interval product of the first `t` rows of `QA` (all equal to `q`). -/
def NuOf (QA : M.S) (m : M.N) (w : M.S) (t : M.N) : Prop :=
  M.le t m ∧ M.len (M.bmod (M.mag w) (M.imul M.zero t QA)) = M.zero ∧
  ∀ t', M.lt t t' → M.le t' m → M.len (M.bmod (M.mag w) (M.imul M.zero t' QA)) ≠ M.zero

/-- `ν_u` of a numerator: `m` for `u = 0`, otherwise `ν` of its magnitude. -/
def NuNum (QA : M.S) (m : M.N) (u : M.S) (t : M.N) : Prop :=
  if M.len u = M.zero then t = m else M.NuOf QA m u t

/-- A nonbias entry `(u,v)` passes normalization: it is valid with components of length at
most `m` (otherwise the stipulated failed state), and its final flag
`f_m = [ν_u < ν_v ∧ m > ν_u]` is zero. -/
def EntryGood (QA : M.S) (m : M.N) (e : M.S) : Prop :=
  M.ValidPair e ∧ M.le (M.len (M.qnum e)) m ∧ M.le (M.len (M.qden e)) m ∧
  ∀ tu tv, M.NuNum QA m (M.qnum e) tu → M.NuOf QA m (M.qden e) tv →
    ¬ (M.lt tu tv ∧ M.lt tu m)

/-- Record entry `λ` is a weight (nonbias) entry: `O_j < λ ≤ O_j + d_j d_{j-1}` for a layer
`1 ≤ j ≤ k+1`, with `O_j` the number of bits of row `j` of the offset set `OA`. -/
def IsWeightEntry (OA N : M.S) (n l : M.N) : Prop :=
  ∃ j', M.le j' (M.depth N) ∧
    M.lt (M.numones (M.len (M.row (M.add j' M.one) OA)) (M.row (M.add j' M.one) OA)) l ∧
    M.le l (M.add (M.numones (M.len (M.row (M.add j' M.one) OA)) (M.row (M.add j' M.one) OA))
      (M.mul (M.dimAt N n (M.add j' M.one)) (M.dimAt N n j')))

/-- `ValGood_q(N,n)`: `Net(N,n)` and no failure flag in the normalization of any nonbias
entry, with `m = |N|` stages; bias denominators unrestricted. -/
def ValGood (q : ℕ) (N : M.S) (n : M.N) : Prop :=
  M.Net N n ∧
  ∃ Qb : M.S, M.IsSet Qb (fun z => ∃ i ∈ qBits q, z = M.numeral i) ∧
  ∃ QA : M.S, M.IsSet QA (fun z => ∃ a i, M.lt a (M.len N) ∧ M.mem i Qb ∧ z = M.pair a i) ∧
  ∃ OA : M.S, M.IsSet OA (fun z => ∃ j' l' i t, M.le j' (M.depth N) ∧ M.lt l' j' ∧
      M.lt i (M.dimAt N n (M.add l' M.one)) ∧ M.le t (M.dimAt N n l') ∧
      z = M.pair (M.add j' M.one) (M.pair (M.add l' M.one) (M.pair i t))) ∧
  ∀ l, M.IsWeightEntry OA N n l → M.EntryGood QA (M.len N) (M.entry N l)

/-! ### The cutoff `p` -/

/-- A polynomial with nonnegative integer coefficients as a number term. -/
def polyM (p₀ : Polynomial ℕ) (m : M.N) : M.N :=
  (p₀.support.sort (· ≤ ·)).foldr
    (fun e acc => M.add (M.mul (M.numeral (p₀.coeff e)) (M.npow m e)) acc) M.zero

/-- `p(m) = p₀(m) + 2^100 (m+2)^40`. -/
def pCut (p₀ : Polynomial ℕ) (m : M.N) : M.N :=
  M.add (M.polyM p₀ m) (M.mul (M.numeral (2 ^ 100)) (M.npow (M.add m (M.numeral 2)) 40))

end Structure

end

end ReLUWitness.Refuter


