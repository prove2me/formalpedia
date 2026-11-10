-- Prove2me | Definitions.Def_SunGroupIso_Class2_MatrixTuple
-- name    : SunGroupIso_Class2_MatrixTuple
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:08:11.4182+00:00
-- url     : https://prove2.me/theorems/4988f3c1-f0c9-45cf-ad28-d4e520ed5ea5
-- title:
--   The Matrix Tuple Construction, the doubling tuple, augmented vectors, $\theta$, $\Gamma$, the update rule (12) and $\Psi$ (§§5.3–5.5)
-- statement:
--   For an extended vector $\vec a$ of a restriction, $\mu=\sum_{i>t}\log_p\mathrm{ord}(\tilde a_i)$ and the block sizes are $n_1=\phi$, $n_2=\psi+\zeta_0+2\mu$, $n_3=\mu$, $n_4=\eta$, $n_5=3$, $m=\sum n_i$. The **Matrix Tuple Construction** (Figure 2) is the tuple of alternating $m\times m$ matrices over $\mathbb Z/p^\tau$ given by its strictly upper entries, in the order of steps 1–11: commutator map for $F$ ($\zeta$ then $\eta$ matrices), power maps for $F$ on $Y$, on $Z_0$ and modulo $Z(G)$ ($\tau$ matrices each; a $1$ in the column of $a_i^{p^j}$ when it is not central; step 2 uses the scaled power coefficients in the central case, while step 3 also assigns its scaled Z₀ coefficients for every i, as printed), the correspondence modulo $Z(G)$ (one matrix), $\rho$ ($\kappa$ matrices), the three auxiliary rows, the correspondence for $Z_0$ ($\zeta_0$), the power maps of $g_1,\dots,g_\gamma$ ($\gamma$), their commutators ($\gamma^2$), and their commutators with $F$ ($\gamma\zeta+\gamma$), each entry scaled as on the page.
--
--   The **doubling** (§5.4) has blocks $n_1,\dots,n_5,n_1,\dots,n_5$; for every matrix $A$ and block pair $i\le j$ it adds $A_{i,i}$ on $D_{i,i}$ and on $D_{5+i,5+i}$ ($i=j$), or $(A_{i,j},A_{j,i})$ on the pairs $(i,j)$, $(i,j+5)$, $(i+5,j)$, $(i+5,j+5)$ ($i<j$). Its **normalized isometries** are the invertible $Q$ with $Q^TDQ=D$ for all $D$ and $Q[m,m]=1$. **Block congruence** of two constructed tuples: equal block sizes and an invertible block-diagonal $Q$ with $Q_5=I$ and $Q^TA_sQ=B_s$ for all $s$.
--
--   §5.5: $L=2m+\zeta$; $d_i=\mathrm{ord}(\tilde a_i)$ ($i\le\phi$), $1$ otherwise; $q_k=\mathrm{ord}(z_k)$, $L_k=q_k/p$, $s_k=\max\{1,q_k/p^{\delta+1}\}$, $h_k=z_k^{s_k}$, $e_k=q_k/s_k$. The **augmented vector** of $\vec c$ is $(c_1,\dots,c_\phi,1,\dots,1,h_1,\dots,h_\zeta)$. For $v_i^{d_i}=(\prod z_k^{\alpha_{i,k}})y_i$, $\theta_{\vec v}[i,k]=\lfloor\alpha_{i,k}/L_k\rfloor\in\mathbb F_p$, and $\ell_{i,k}=\alpha_{i,k}\bmod L_k$ read off $\vec x$, the augmented $\vec a$. **$\Gamma$** contains $\mathrm{diag}(Q_T,Q_T,I_\zeta)$ for $T\in\Gamma_1$ ($Q_T$ the first-copy block-diagonal part), $I_L+\frac{e_k}{pd_i}E_{2m+k,i}$ for $t<i\le\phi$ with $q_k>d_i$, and $I_L+\frac{e_k}{p}E_{2m+k,\psi+j}$ for $j\le\zeta_0$. The **update rule (12)** is $P(\theta)[i,k]\equiv\sum_jc_{ij}\theta[j,k]+\lfloor(\sum_jc_{ij}\ell_{j,k}+\binom{d_i}{2}\sum_{j<r}\hat P[j,i]\hat P[r,i]\beta_{r,j,k})/L_k\rfloor\pmod p$ with $c_{ij}=d_i\hat P[j,i]/d_j$. **$\Psi$** is the least set containing $\theta_{\vec x}$ and closed under $P(\cdot)$ for every $P\in\Gamma$.
--
--   **Formalization Note** Matrices are one-based entry functions with a block-size list. Scaled entries such as $(\xi p^j/\mathrm{ord}(\tilde a_i))\cdot p^{\tau+1}/\mathrm{ord}(z)$, which the page asserts to be integers, are computed as one natural-number quotient. The doubling adds the block matrices of every block pair, zero or not; a zero matrix constrains no isometry, so the isometries are those of the page's tuple whenever the two tuples have the same nonzero pattern.
--
--   Figure 2 step 3’s “and set” is an independent assignment, including when a_i^(p^j) is noncentral. This differs from the draft’s former “otherwise” branch; the resulting issue in the proof of Lemma 5.26 is recorded in I5.
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), §§5.3–5.5, pp. 34–52 (PDF 36–54)

import Mathlib
import Definitions.Def_SunGroupIso_Class2_ExtVector

set_option autoImplicit false

noncomputable section

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

/-- A tuple of square matrices with a block structure: `dims` lists the block sizes
(`n_1, …, n_5` on the page), and each matrix is given by its one-based entries `A[i, j]`,
`1 ≤ i, j ≤ Σ dims`. -/
structure MatTuple (R : Type*) where
  dims : List ℕ
  mats : List (ℕ → ℕ → R)

/-- The dimension `m = n_1 + ⋯ + n_5`. -/
def MatTuple.size {R : Type*} (T : MatTuple R) : ℕ := T.dims.sum

/-- The `M × M` matrix of one-based entries. -/
def toMat {R : Type*} (M : ℕ) (A : ℕ → ℕ → R) : Matrix (Fin M) (Fin M) R :=
  fun i j => A (i.val + 1) (j.val + 1)

/-- One-based entry `P[i, j]` of a square matrix (`0` outside). -/
def entry1 {R : Type*} [Zero R] {S : ℕ} (P : Matrix (Fin S) (Fin S) R) (i j : ℕ) : R :=
  if h : 1 ≤ i ∧ i ≤ S ∧ 1 ≤ j ∧ j ≤ S then P ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ else 0

/-- The alternating matrix with prescribed strictly upper-triangular entries `u` (Matrix Tuple
Construction, p. 35: "we specify only its strictly upper-triangular entries … A[j,i] = −A[i,j] for
i < j, and all diagonal entries are zero"). -/
def altOf {R : Type*} [Neg R] [Zero R] (u : ℕ → ℕ → R) : ℕ → ℕ → R :=
  fun i j => if i < j then u i j else if j < i then -u j i else 0

/-- The (zero-based) number of the block containing the one-based index `i`. -/
def blockOf (dims : List ℕ) (i : ℕ) : ℕ :=
  ((List.range dims.length).filter fun b => (dims.take (b + 1)).sum < i).length

variable {G : Type*} [Group G] {p ζ γ κ τ : ℕ}

section MTC

variable (r : Restriction G p ζ γ κ τ) {n : ℕ} (a : Fin n → G)

/-- `ord(ã_i)`. -/
def dq (i : ℕ) : ℕ := orderOf (tl (at1 a i))

/-- `log_p ord(ã_i)`. -/
def lgq (i : ℕ) : ℕ := Nat.log p (dq a i)

/-- `t = ψ + ζ_0`. -/
def tt : ℕ := r.psi + r.zeta0

/-- `µ = Σ_{i=t+1}^{ϕ} log_p ord(ã_i)` (p. 34, PDF p. 36). -/
def mu : ℕ := ∑ i ∈ Finset.Ioc (tt r) n, lgq (p := p) a i

/-- The position (one-based, in `[1, µ]`) of `a_i^{p^j}` in `s⃗_p = (a_{t+1}, a_{t+1}^p, …,
a_{t+1}^{ord(ã_{t+1})/p}, …, a_ϕ, …, a_ϕ^{ord(ã_ϕ)/p})`, for `t < i ≤ ϕ` and `p^j < ord(ã_i)`. -/
def spIdx (i j : ℕ) : ℕ := (∑ i' ∈ Finset.Ioo (tt r) i, lgq (p := p) a i') + j + 1

/-- `m_2 = m_1 + ψ + ζ_0 + 2µ`. -/
def m2 : ℕ := n + tt r + 2 * mu r a
/-- `m_3 = m_2 + µ`. -/
def m3 : ℕ := m2 r a + mu r a
/-- `m_4 = m_3 + η`. -/
def m4 : ℕ := m3 r a + r.eta
/-- `m = m_5 = m_4 + 3`. -/
def mm : ℕ := m4 r a + 3

/-- Coefficient `x_{i,j}` of `ã_i` on `ã_{t+j}` in `⟨F,Z(G)⟩/Z(G) = ⊕_{j=1}^{η} ⟨ã_{t+j}⟩` (step 5). -/
def xco (i j : ℕ) : ℕ :=
  atN (coeffsWith (fun j : Fin r.eta => tl (at1 a (tt r + j.val + 1))) ⊥ (tl (at1 a i))) (j - 1)

/-- A natural number as an element of `R = Z/p^τZ`. -/
abbrev cR (x : ℕ) : ZMod (p ^ τ) := (x : ZMod (p ^ τ))

/-- Step 1, first part, matrix `k ∈ [ζ]`: `A_k[i,j] = α_{γ+i,γ+j,k} · p^τ/ord(z_k)` for `i < j ≤ ϕ`. -/
def step1a (k : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i j =>
  if 1 ≤ i ∧ i < j ∧ j ≤ n then
    cR (alphaC r a (γ + i) (γ + j) k * p ^ τ / orderOf (at1 r.z k)) else 0

/-- Step 1, second part, matrix `j ∈ [η]`: `A_j[i, m_1+ℓ] = β_{γ+i, γ+ψ+ζ_0+j, ℓ} · p^τ/ord(a_ℓ)`. -/
def step1b (jj : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if 1 ≤ i ∧ i ≤ n ∧ n + 1 ≤ c ∧ c ≤ n + r.psi then
    cR (betaC r a (γ + i) (γ + tt r + jj) (c - n) * (p ^ τ / orderOf (at1 a (c - n))))
  else 0

/-- Step 2 (power map for `F` on `Y`), matrix `j + 1`, `0 ≤ j < τ`: if `a_i^{p^j} ∉ Z(G)`, a `1` in the
column of the second block's first `s⃗_p` copy for `a_i^{p^j}`; otherwise
`A[i, m_1+ℓ] = (π_{γ+i,ℓ} · p^j/ord(ã_i)) · p^τ/ord(a_ℓ)` for `ℓ ∈ [ψ]`. -/
def step2 (j : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if 1 ≤ i ∧ i ≤ n then
    (if p ^ j < dq a i then (if c = n + tt r + spIdx r a i j then 1 else 0)
     else if n + 1 ≤ c ∧ c ≤ n + r.psi then
       cR (piC r a (γ + i) (c - n) * (p ^ j / dq a i) * (p ^ τ / orderOf (at1 a (c - n))))
     else 0)
  else 0

/-- Step 3 (power map for `F` on `Z_0`), matrix `j + 1`: if `a_i^{p^j} ∉ Z(G)`, a `1` in the column of
the second `s⃗_p` copy; also set `A[i, m_1+ψ+h] = (ξ_{γ+i,ζ−ζ_0+h} · p^j/ord(ã_i)) · p^{τ+1}/ord(z_{ζ−ζ_0+h})`
for `h ∈ [ζ_0]` (the rational product, an integer on the page, computed as one quotient). -/
def step3 (j : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if 1 ≤ i ∧ i ≤ n then
    (if p ^ j < dq a i ∧ c = n + tt r + mu r a + spIdx r a i j then 1
     else if n + r.psi + 1 ≤ c ∧ c ≤ n + r.psi + r.zeta0 then
       cR (xiC r a (γ + i) (r.bigIdx (c - n - r.psi) + 1) * p ^ j * p ^ (τ + 1) /
         (dq a i * orderOf (r.zBig (c - n - r.psi))))
     else 0)
  else 0

/-- Step 4 (power map modulo `Z(G)`), matrix `j + 1`: a `1` in the third-block column of `a_i^{p^j}`. -/
def step4 (j : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if 1 ≤ i ∧ i ≤ n ∧ p ^ j < dq a i ∧ c = m2 r a + spIdx r a i j then 1 else 0

/-- Step 5 (correspondence modulo `Z(G)`): `A[i, m_3+j] = x_{i,j} · p^τ/ord(ã_{ψ+ζ_0+j})`. -/
def step5 : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if 1 ≤ i ∧ i ≤ n ∧ m3 r a + 1 ≤ c ∧ c ≤ m3 r a + r.eta then
    cR (xco r a i (c - m3 r a) * (p ^ τ / dq a (tt r + (c - m3 r a))))
  else 0

/-- Step 6 (`ρ` value), matrix `s ∈ [κ]`: `A_s[i, m]` is the `s`-th coordinate of `ρ(a_i)`. -/
def step6 (s : Fin κ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if 1 ≤ i ∧ i ≤ n ∧ c = mm r a then r.ρ (at1 a i) s else 0

/-- Step 7 (auxiliary three rows): `A_1[m−2, m−1] = 1`, `A_2[m−2, m] = 1`, `A_3[m−1, m] = 1`. -/
def step7 (u v : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c => if i = u ∧ c = v then 1 else 0

/-- Step 8 (correspondence for `Z_0`), matrix `k ∈ [ζ_0]`: `A_k[m_1+ψ+k, m] = 1`. -/
def step8 (k : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if i = n + r.psi + k ∧ c = mm r a then 1 else 0

/-- Step 9 (power map for `g_1, …, g_γ`), matrix `ℓ ∈ [γ]`: `A_ℓ[m_1+i, m] = π_{ℓ,i} · p^τ/ord(a_i)`. -/
def step9 (l : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if n + 1 ≤ i ∧ i ≤ n + r.psi ∧ c = mm r a then
    cR (piC r a l (i - n) * (p ^ τ / orderOf (at1 a (i - n)))) else 0

/-- Step 10 (commutator map for `g_1, …, g_γ`), matrix `(i, j) ∈ [γ]²`:
`A[m_1+ℓ, m] = β_{i,j,ℓ} · p^τ/ord(a_ℓ)`. -/
def step10 (ii jj : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if n + 1 ≤ i ∧ i ≤ n + r.psi ∧ c = mm r a then
    cR (betaC r a ii jj (i - n) * (p ^ τ / orderOf (at1 a (i - n)))) else 0

/-- Step 11, first part, matrix `(j, k) ∈ [γ] × [ζ]`: `A[i, m] = α_{γ+i,j,k} · p^τ/ord(z_k)`. -/
def step11a (jj k : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if 1 ≤ i ∧ i ≤ n ∧ c = mm r a then
    cR (alphaC r a (γ + i) jj k * p ^ τ / orderOf (at1 r.z k)) else 0

/-- Step 11, second part, matrix `j ∈ [γ]`: `A[i, m_1+ℓ] = β_{γ+i,j,ℓ} · p^τ/ord(a_ℓ)`. -/
def step11b (jj : ℕ) : ℕ → ℕ → ZMod (p ^ τ) := altOf fun i c =>
  if 1 ≤ i ∧ i ≤ n ∧ n + 1 ≤ c ∧ c ≤ n + r.psi then
    cR (betaC r a (γ + i) jj (c - n) * (p ^ τ / orderOf (at1 a (c - n)))) else 0

/-- **The Matrix Tuple Construction** (§5.3 and Figure 2, pp. 34–36, PDF pp. 36–38): the alternating
tuple over `R = Z/p^τZ` built from an extended vector `a⃗`, with blocks
`n_1 = ϕ, n_2 = ψ + ζ_0 + 2µ, n_3 = µ, n_4 = η, n_5 = 3`, and its matrices in the order of steps 1–11. -/
def mtc : MatTuple (ZMod (p ^ τ)) where
  dims := [n, tt r + 2 * mu r a, mu r a, r.eta, 3]
  mats :=
    (List.range ζ).map (fun k => step1a r a (k + 1)) ++
    (List.range r.eta).map (fun j => step1b r a (j + 1)) ++
    (List.range τ).map (step2 r a) ++
    (List.range τ).map (step3 r a) ++
    (List.range τ).map (step4 r a) ++
    [step5 r a] ++
    (List.finRange κ).map (step6 r a) ++
    [step7 (mm r a - 2) (mm r a - 1), step7 (mm r a - 2) (mm r a), step7 (mm r a - 1) (mm r a)] ++
    (List.range r.zeta0).map (fun k => step8 r a (k + 1)) ++
    (List.range γ).map (fun l => step9 r a (l + 1)) ++
    ((List.range γ).flatMap fun i => (List.range γ).map fun j => step10 r a (i + 1) (j + 1)) ++
    ((List.range γ).flatMap fun j => (List.range ζ).map fun k => step11a r a (j + 1) (k + 1)) ++
    (List.range γ).map (fun j => step11b r a (j + 1))

end MTC

section Doubling

variable {R : Type*} [CommRing R]

/-- One matrix of the doubling: the blocks `(b, b')` and `(b', b)` of `A`, placed in copy `c` (rows of
block `b`) and copy `c'` (columns of block `b'`) of the doubled index set, zero elsewhere. -/
def dblEntry (M : ℕ) (dims : List ℕ) (A : ℕ → ℕ → R) (b b' c c' : ℕ) : ℕ → ℕ → R := fun i j =>
  let ci := if i ≤ M then 0 else 1
  let cj := if j ≤ M then 0 else 1
  let i0 := if i ≤ M then i else i - M
  let j0 := if j ≤ M then j else j - M
  if (blockOf dims i0 = b ∧ ci = c ∧ blockOf dims j0 = b' ∧ cj = c') ∨
      (blockOf dims i0 = b' ∧ ci = c' ∧ blockOf dims j0 = b ∧ cj = c) then A i0 j0 else 0

/-- **The doubling matrix tuple** (§5.4, p. 47, PDF p. 49): blocks `n_1, …, n_5, n_1, …, n_5`; for each
matrix `A` of the tuple and each block pair `i ≤ j` of `[5]`: for `i = j`, the two matrices carrying
`A_{i,i}` on `D_{i,i}` and on `D_{5+i,5+i}`; for `i < j`, the four matrices carrying `(A_{i,j}, A_{j,i})` on
the block pairs `(i, j)`, `(i, j+5)`, `(i+5, j)`, `(i+5, j+5)`. -/
def doubling (T : MatTuple R) : MatTuple R where
  dims := T.dims ++ T.dims
  mats := T.mats.flatMap fun A =>
    (List.range 5).flatMap fun b => ((List.range 5).filter fun b' => b ≤ b').flatMap fun b' =>
      if b = b' then [dblEntry T.size T.dims A b b 0 0, dblEntry T.size T.dims A b b 1 1]
      else [dblEntry T.size T.dims A b b' 0 0, dblEntry T.size T.dims A b b' 0 1,
            dblEntry T.size T.dims A b b' 1 0, dblEntry T.size T.dims A b b' 1 1]

/-- `Q = diag(Q_1, …, Q_k)` is block diagonal for the block sizes `dims`. -/
def IsBlockDiag (dims : List ℕ) {M : ℕ} (Q : Matrix (Fin M) (Fin M) R) : Prop :=
  ∀ i j : Fin M, blockOf dims (i.val + 1) ≠ blockOf dims (j.val + 1) → Q i j = 0

/-- The fifth diagonal block `Q_5` is the identity matrix. -/
def FifthBlockId (dims : List ℕ) {M : ℕ} (Q : Matrix (Fin M) (Fin M) R) : Prop :=
  ∀ i j : Fin M, blockOf dims (i.val + 1) = 4 → blockOf dims (j.val + 1) = 4 →
    Q i j = if i = j then 1 else 0

/-- **Block-diagonal congruence with `Q_5 = I`** (Lemma 5.12): the two tuples have the same block sizes
and an invertible block-diagonal `Q` with `Q_5 = I` has `Qᵀ A_s Q = B_s` for every `s`. -/
def BlockCongruent (A B : MatTuple R) : Prop :=
  A.dims = B.dims ∧
  ∃ Q : Matrix (Fin A.size) (Fin A.size) R, IsUnit Q ∧ IsBlockDiag A.dims Q ∧ FifthBlockId A.dims Q ∧
    List.Forall₂ (fun X Y => Q.transpose * toMat A.size X * Q = toMat A.size Y) A.mats B.mats

/-- **The normalized isometries of a doubled tuple** (Lemma 5.24): the invertible `Q` with
`Qᵀ D Q = D` for every matrix `D` of the tuple and `Q[m, m] = 1`, `m` the size of one copy. -/
def normIsoSet (D : MatTuple R) (m : ℕ) : Set (GL (Fin D.size) R) :=
  {P | (∀ X ∈ D.mats,
      (P : Matrix (Fin D.size) (Fin D.size) R).transpose * toMat D.size X * P = toMat D.size X) ∧
    entry1 (P : Matrix (Fin D.size) (Fin D.size) R) m m = 1}

end Doubling

section Orbit

variable (δ : ℕ) (r : Restriction G p ζ γ κ τ) {n : ℕ} (a : Fin n → G)

/-- `m`, the size of the Matrix Tuple Construction of `a⃗`. -/
def Mdim : ℕ := (mtc r a).size

/-- `L = 2m + ζ` (§5.5, p. 49, PDF p. 51). -/
def Ldim : ℕ := 2 * Mdim r a + ζ

/-- `d_i = ord(ã_i)` for `i ≤ ϕ`, `d_i = 1` for `ϕ < i ≤ L`. -/
def dA (i : ℕ) : ℕ := if 1 ≤ i ∧ i ≤ n then orderOf (tl (at1 a i)) else 1

/-- `q_k = ord(z_k)`. -/
def qk (k : ℕ) : ℕ := orderOf (at1 r.z k)
/-- `L_k = q_k/p`. -/
def Lk (k : ℕ) : ℕ := qk r k / p
/-- `s_k = max{1, q_k/p^{δ+1}}`. -/
def sk (k : ℕ) : ℕ := max 1 (qk r k / p ^ (δ + 1))
/-- `h_k = z_k^{s_k}`. -/
def hk (k : ℕ) : G := at1 r.z k ^ sk δ r k
/-- `e_k = ord(h_k) = q_k/s_k`. -/
def ek (k : ℕ) : ℕ := qk r k / sk δ r k

/-- **Augmented vector** of `c⃗` (§5.5 item 2): `(c_1, …, c_ϕ, 1, …, 1, h_1, …, h_ζ) ∈ G^L`. -/
def augment (c : Fin n → G) : Fin (Ldim r a) → G := fun i =>
  if i.val + 1 ≤ n then at1 c (i.val + 1)
  else if i.val + 1 ≤ 2 * Mdim r a then 1 else hk δ r (i.val + 1 - 2 * Mdim r a)

/-- `α_{i,k}`: the `z_k`-coefficient of `v_i^{d_i} = (∏_k z_k^{α_{i,k}}) y_i`, `y_i ∈ Y`, `0 ≤ α_{i,k} < q_k`. -/
def alphaAug (v : Fin (Ldim r a) → G) (i k : ℕ) : ℕ :=
  atN (coeffsWith r.z r.Y (at1 v i ^ dA a i)) (k - 1)

/-- **The highest-digit matrix** `θ_v⃗[i,k] = (α_{i,k} − ℓ_{i,k})/L_k ∈ F_p`, `ℓ_{i,k} = α_{i,k} mod L_k`
(§5.5 item 3). -/
def theta (v : Fin (Ldim r a) → G) : Fin (Ldim r a) → Fin ζ → ZMod p :=
  fun i k => ((alphaAug r a v (i.val + 1) (k.val + 1) / Lk r (k.val + 1) : ℕ) : ZMod p)

/-- The fixed residues `ℓ_{j,k} = α_{j,k} mod L_k`, read off the augmented vector `x⃗` of `a⃗`. -/
def ellRes (j k : ℕ) : ℕ := alphaAug r a (augment δ r a a) j k % Lk r k

/-- `β_{ℓ,j,k}`: the `z_k`-coefficient of `[a_ℓ, a_j]` for `ℓ, j ≤ ϕ`, and `0` otherwise (p. 51). -/
def betaAug (l j k : ℕ) : ℕ :=
  if 1 ≤ l ∧ l ≤ n ∧ 1 ≤ j ∧ j ≤ n then atN (coeffsWith r.z r.Y ⁅at1 a l, at1 a j⁆) (k - 1) else 0

/-- `Q_T = diag(T_{1,1}, …, T_{5,5})`, the first-copy block-diagonal part of a doubled-tuple
isometry `T`, one-based on `[1, m]`. -/
def blockPart {S : ℕ} (T : Matrix (Fin S) (Fin S) (ZMod (p ^ τ))) : ℕ → ℕ → ZMod (p ^ τ) :=
  fun i j => if 1 ≤ i ∧ i ≤ Mdim r a ∧ 1 ≤ j ∧ j ≤ Mdim r a ∧
      blockOf (mtc r a).dims i = blockOf (mtc r a).dims j then entry1 T i j else 0

/-- `diag(Q, Q, I_ζ)` as an `L × L` matrix. -/
def liftGen (Q : ℕ → ℕ → ZMod (p ^ τ)) : Matrix (Fin (Ldim r a)) (Fin (Ldim r a)) (ZMod (p ^ τ)) :=
  fun i j =>
    if i.val + 1 ≤ Mdim r a ∧ j.val + 1 ≤ Mdim r a then Q (i.val + 1) (j.val + 1)
    else if Mdim r a < i.val + 1 ∧ i.val + 1 ≤ 2 * Mdim r a ∧ Mdim r a < j.val + 1 ∧
        j.val + 1 ≤ 2 * Mdim r a then Q (i.val + 1 - Mdim r a) (j.val + 1 - Mdim r a)
    else if 2 * Mdim r a < i.val + 1 ∧ 2 * Mdim r a < j.val + 1 then (if i = j then 1 else 0)
    else 0

/-- `I_L + c · E_{row, col}` (one-based). -/
def elemGen (row col c : ℕ) : Matrix (Fin (Ldim r a)) (Fin (Ldim r a)) (ZMod (p ^ τ)) :=
  fun i j => (if i = j then 1 else 0) + (if i.val + 1 = row ∧ j.val + 1 = col then (c : ZMod (p ^ τ)) else 0)

/-- **The generator list `Γ`** (§5.5 item 4, p. 50, PDF p. 52): `diag(Q_T, Q_T, I_ζ)` for each `T ∈ Γ_1`;
`I_L + (e_k/(p d_i)) E_{2m+k, i}` for `t < i ≤ ϕ`, `k ∈ [ζ]` with `q_k > d_i`; and
`I_L + (e_k/p) E_{2m+k, ψ+j}`, `k = ζ − ζ_0 + j`, for `j ∈ [ζ_0]`. -/
def gammaList (Γ1 : List (GL (Fin (doubling (mtc r a)).size) (ZMod (p ^ τ)))) :
    List (Matrix (Fin (Ldim r a)) (Fin (Ldim r a)) (ZMod (p ^ τ))) :=
  Γ1.map (fun T => liftGen r a (blockPart r a T.val)) ++
  ((List.range (n - tt r)).flatMap fun i0 =>
    (List.range ζ).filterMap fun k0 =>
      if dA a (tt r + i0 + 1) < qk r (k0 + 1) then
        some (elemGen r a (2 * Mdim r a + k0 + 1) (tt r + i0 + 1)
          (ek δ r (k0 + 1) / (p * dA a (tt r + i0 + 1))))
      else none) ++
  (List.range r.zeta0).map fun j0 =>
    elemGen r a (2 * Mdim r a + r.bigIdx (j0 + 1) + 1) (r.psi + j0 + 1)
      (ek δ r (r.bigIdx (j0 + 1) + 1) / p)

/-- **The update rule (12)** (p. 51, PDF p. 53): with `P̂[j,i] ∈ [0, p^τ)` and `c_{ij}(P) = d_i P̂[j,i]/d_j`,
`P(θ)[i,k] ≡ Σ_j c_{ij} θ[j,k] + ⌊(Σ_j c_{ij} ℓ_{j,k} + C(d_i, 2) Σ_{1≤j<r≤L} P̂[j,i] P̂[r,i] β_{r,j,k})/L_k⌋
(mod p)`, all arithmetic over the integers with representatives `0, …, p−1` for `θ`. -/
def updTheta (P : Matrix (Fin (Ldim r a)) (Fin (Ldim r a)) (ZMod (p ^ τ)))
    (θ : Fin (Ldim r a) → Fin ζ → ZMod p) : Fin (Ldim r a) → Fin ζ → ZMod p :=
  fun i k =>
    let Ph : ℕ → ℕ := fun j => (entry1 P j (i.val + 1)).val
    let c : ℕ → ℕ := fun j => dA a (i.val + 1) * Ph j / dA a j
    let s1 : ℕ := ∑ j : Fin (Ldim r a), c (j.val + 1) * (θ j k).val
    let s2 : ℕ := ∑ j : Fin (Ldim r a), c (j.val + 1) * ellRes δ r a (j.val + 1) (k.val + 1)
    let s3 : ℕ := Nat.choose (dA a (i.val + 1)) 2 *
      ∑ j : Fin (Ldim r a), ∑ rr : Fin (Ldim r a),
        if j < rr then Ph (j.val + 1) * Ph (rr.val + 1) * betaAug r a (rr.val + 1) (j.val + 1) (k.val + 1)
        else 0
    ((s1 + (s2 + s3) / Lk r (k.val + 1) : ℕ) : ZMod p)

end Orbit

/-- The orbit closure: the least set containing `x0` and closed under every map in `fs`. -/
inductive InOrbit {X : Type*} (x0 : X) (fs : List (X → X)) : X → Prop
  | base : InOrbit x0 fs x0
  | step {x : X} (f : X → X) : f ∈ fs → InOrbit x0 fs x → InOrbit x0 fs (f x)

/-- **`Ψ`** (Group Restriction Isomorphism Algorithm, steps 4–5, p. 52, PDF p. 54): start from
`{θ_x⃗}` and add `P(θ)` for every `θ ∈ Ψ` and `P ∈ Γ` until nothing changes — the least set containing
`θ_x⃗` and closed under the update rule of every generator. -/
def Psi (δ : ℕ) (r : Restriction G p ζ γ κ τ) {n : ℕ} (a : Fin n → G)
    (Γ1 : List (GL (Fin (doubling (mtc r a)).size) (ZMod (p ^ τ)))) :
    Set (Fin (Ldim r a) → Fin ζ → ZMod p) :=
  {θ | InOrbit (theta r a (augment δ r a a)) ((gammaList δ r a Γ1).map (updTheta δ r a)) θ}

end SunGroupIso.Class2


