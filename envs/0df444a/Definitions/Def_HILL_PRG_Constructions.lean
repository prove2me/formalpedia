-- Prove2me | Definitions.Def_HILL_PRG_Constructions
-- name    : HILL_PRG_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:02.537489+00:00
-- url     : https://prove2.me/theorems/b61300da-3dd4-411c-9d7b-2e57ea76139e
-- title:
--   Constructions 4.13 and (6.1)–(6.8)
-- statement:
--   Construction 4.13 repeats a pseudoentropy generator $k_n$ times and hashes the concatenated outputs with an independent public key. Its repetition count and integer output length are
--
--   $$
--   k_n=\left\lceil\frac{2m_n+1}{s_n}\right\rceil^3,\qquad
--   j_n=\left\lfloor k_n(n+s_n)-2m_n k_n^{2/3}\right\rfloor.
--   $$
--
--   For Section 6, $\widetilde D_f(z)$ is the ceiling of the base-two logarithm of the number of preimages of $z$. The set $\mathcal T$ consists of pairs $(x,i)$ with $i\le\widetilde D_f(f(x))$. The parameter $p_n$ is the fraction of pairs in $\mathcal T$, and $m_n=\lfloor k_np_n-2k_n^{2/3}\rfloor$. The finite seed contains $k_n$ independent $n$-bit strings, indices, hash keys, and independent $n$-bit masks. The output includes a universal hash of the $k_n$ parity bits, the repeated $f'$ outputs, the public key, and the masks. A comparison output replaces the first hash block by independent uniform bits.
--
--   The constructions make the paper's probability spaces and entropy comparison explicit for the later milestones.
--
--   **Formalization Note** Equation (6.8) prints $I'$ as unconstrained bit blocks, while (6.3) defines $f'$ only for $i<n$ and (6.5) uses indices uniform on $\{0,\ldots,n-1\}$. Each index is therefore `Fin n`, and the output is compared on a finite product seed. Prefixes in $f'$ are retained as structured fields for entropy, and padded for the fixed-width binary computational law. The real-valued (6.6) output length is rounded down. The advice for Section 6 is this integer output length $m_n$.
-- source:
--   Håstad, Impagliazzo, Levin and Luby, A pseudorandom generator from any one-way function, SIAM J. Comput. 28(4), 1999, pp. 1370, 1380, 1385–1387, Definition 2.13, Construction 4.13 and equations (6.1)–(6.8)

import Mathlib
import Definitions.Def_HILL_PRG_Model

namespace HILL.PRG

/-- The i-th fixed-length block of a bit string. -/
def block (w : Bits) (i d : ℕ) : Bits := (w.drop (i * d)).take d

/-- The repetition count in Construction 4.13. -/
noncomputable def k413 (F : FunEns) (s : ℕ → ℝ) (n : ℕ) : ℕ :=
  (Nat.ceil (((2 * (F.ℓ n : ℝ) + 1) / s n))) ^ 3

/-- The rounded output length in Construction 4.13. -/
noncomputable def j413 (F : FunEns) (s : ℕ → ℝ) (n : ℕ) : ℕ :=
  Nat.floor ((k413 F s n : ℝ) * ((n : ℝ) + s n) -
    2 * (F.ℓ n : ℝ) * (k413 F s n : ℝ) ^ ((2 : ℝ) / 3))

/-- Construction 4.13: keyed universal hashing of independent copies of f. -/
noncomputable def construction413 (F : FunEns) (s : ℕ → ℝ)
    (h : HashFamily) : FunEns where
  t n := k413 F s n * n + h.keyLen n
  ℓ n := j413 F s n + h.keyLen n
  f a n w :=
    let key := w.drop (k413 F s n * n)
    let outputs := (List.range (k413 F s n)).flatMap
      (fun i => F.f a n (block w i n))
    h.eval n key outputs ++ key

/-- The restricted pair set 𝒯 from Section 6.1. -/
def T64 (F : FunEns) (n : ℕ) : Finset (Bits × Fin n) :=
  (cube n ×ˢ Finset.univ).filter
    (fun z => z.2.val ≤ Dtilde (cube n) (F.f 0 n) (F.f 0 n z.1))

/-- Equation (6.5), with the index uniform on {0,…,n−1}. -/
noncomputable def p64 (F : FunEns) (n : ℕ) : ℝ :=
  (T64 F n).card / ((cube n).card * n : ℕ)

/-- Equation (6.6), rounded down to an integer number of output bits. -/
noncomputable def m64 (F : FunEns) (k : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.floor ((k n : ℝ) * p64 F n - 2 * (k n : ℝ) ^ ((2 : ℝ) / 3))

/-- One sample from the finite product seed in (6.8). -/
structure Seed64 (n k r u : ℕ) where
  X : Fin k → Fin n → Bool
  I : Fin k → Fin n
  R : Fin k → Fin r → Bool
  U : Fin u → Bool
  Y : Fin k → Fin n → Bool
  deriving DecidableEq

noncomputable instance (n k r u : ℕ) : Fintype (Seed64 n k r u) := by
  classical
  let e : Seed64 n k r u ≃
      (Fin k → Fin n → Bool) × (Fin k → Fin n) ×
      (Fin k → Fin r → Bool) × (Fin u → Bool) × (Fin k → Fin n → Bool) := {
    toFun := fun s => (s.X, s.I, s.R, s.U, s.Y)
    invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
    left_inv := by intro s; cases s; rfl
    right_inv := by intro p; rcases p with ⟨a,b,c,d,e⟩; rfl
  }
  exact Fintype.ofEquiv _ e.symm

/-- A structured version of f′(x,i,r), with its variable prefix kept separate. -/
def fPrime64 (F : FunEns) (h : HashFamily) (n : ℕ)
    (x : Fin n → Bool) (i : Fin n) (r : Fin (h.keyLen n) → Bool) :
    Bits × Bits × Fin n × Bits :=
  (F.f 0 n (List.ofFn x),
    (h.eval n (List.ofFn r) (List.ofFn x)).take (i.val + Nat.clog 2 (2 * n)),
    i, List.ofFn r)

/-- The structured output of (6.8); tuples retain the length and index boundaries. -/
def Out64 (n k : ℕ) :=
  Bits × (Fin k → Bits × Bits × Fin n × Bits) × Bits × (Fin k → Fin n → Bool)

/-- The output distribution 𝒟 of (6.8), before converting to a bit-string encoding. -/
def outD64 (F : FunEns) (h hp : HashFamily) (n k : ℕ)
    (seed : Seed64 n k (h.keyLen n) (hp.keyLen n)) : Out64 n k :=
  (hp.eval n (List.ofFn seed.U)
      (List.ofFn (fun j : Fin k => ip (List.ofFn (seed.X j)) (List.ofFn (seed.Y j)))),
    (fun j => fPrime64 F h n (seed.X j) (seed.I j) (seed.R j)),
    List.ofFn seed.U, seed.Y)

/-- The comparison distribution ℰ: replace the first m bits by independent uniform bits. -/
def outE64 (F : FunEns) (h hp : HashFamily) (n k m : ℕ)
    (seed : Seed64 n k (h.keyLen n) (hp.keyLen n)) (z : Fin m → Bool) : Out64 n k :=
  (List.ofFn z,
    (fun j => fPrime64 F h n (seed.X j) (seed.I j) (seed.R j)),
    List.ofFn seed.U, seed.Y)

/-- The joint law of a weighted source and a uniform independent hash key. -/
noncomputable def hashJoint (D : Bits → ℝ) (h : HashFamily) (n : ℕ)
    (y : Bits × Bits) : ℝ :=
  weightedLaw (cube n ×ˢ cube (h.keyLen n))
    (fun z => D z.1 / ((cube (h.keyLen n)).card : ℝ))
    (fun z => (h.eval n z.2 z.1, z.2)) y

/-- Uniform joint law on an output string and a hash key. -/
noncomputable def hashUniform (h : HashFamily) (n : ℕ)
    (y : Bits × Bits) : ℝ :=
  uniformBits (h.outLen n) y.1 * uniformBits (h.keyLen n) y.2

/-- The two exact Shannon entropies in Lemma 6.4. -/
noncomputable def entropyD64 (F : FunEns) (h hp : HashFamily) (n k : ℕ) : ℝ :=
  by
  classical
  exact entropyOf Finset.univ (outD64 F h hp n k)

noncomputable def entropyE64 (F : FunEns) (h hp : HashFamily) (n k m : ℕ) : ℝ :=
  by
  classical
  exact entropyOf (Finset.univ : Finset (Seed64 n k (h.keyLen n) (hp.keyLen n) ×
    (Fin m → Bool))) (fun z => outE64 F h hp n k m z.1 z.2)

/-- A concrete binary encoding of a Section 6 seed, with unary index blocks. -/
def encodeSeed64 {n k r u : ℕ} (seed : Seed64 n k r u) : Bits :=
  ((List.finRange k).flatMap (fun j => List.ofFn (seed.X j))) ++
  ((List.finRange k).flatMap (fun j =>
    List.replicate (seed.I j).val true ++
      [false] ++ List.replicate (n - (seed.I j).val - 1) false)) ++
  ((List.finRange k).flatMap (fun j => List.ofFn (seed.R j))) ++
  List.ofFn seed.U ++
  ((List.finRange k).flatMap (fun j => List.ofFn (seed.Y j)))

/-- Pad a prefix to its declared bit length. -/
def padTo (w : Bits) (d : ℕ) : Bits :=
  w.take d ++ List.replicate (d - (w.take d).length) false

/-- A fixed n-bit unary encoding of an index in {0,…,n−1}. -/
def indexBits {n : ℕ} (i : Fin n) : Bits :=
  List.replicate i.val true ++ [false] ++ List.replicate (n - i.val - 1) false

/-- Binary encoding of the structured output, with fixed field widths. -/
def encodeOut64 (F : FunEns) (h hp : HashFamily) (n k : ℕ)
    (o : Out64 n k) : Bits :=
  padTo o.1 (hp.outLen n) ++
  ((List.finRange k).flatMap (fun j =>
    let q := o.2.1 j
    padTo q.1 (F.ℓ n) ++ padTo q.2.1 (h.outLen n) ++
      indexBits q.2.2.1 ++ padTo q.2.2.2 (h.keyLen n))) ++
  padTo o.2.2.1 (hp.keyLen n) ++
  ((List.finRange k).flatMap (fun j => List.ofFn (o.2.2.2 j)))

/-- The output length of the fixed-width binary encoding of (6.8). -/
def outLen64 (F : FunEns) (h hp : HashFamily) (n k : ℕ) : ℕ :=
  hp.outLen n + k * (F.ℓ n + h.outLen n + n + h.keyLen n) +
    hp.keyLen n + k * n

/-- The binary law of (6.8) on the finite product seed. -/
noncomputable def binaryLawD64 (F : FunEns) (h hp : HashFamily) (n k : ℕ)
    (y : Bits) : ℝ :=
  lawOn Finset.univ (fun seed : Seed64 n k (h.keyLen n) (hp.keyLen n) =>
    encodeOut64 F h hp n k (outD64 F h hp n k seed)) y

/-- The binary comparison law with fresh uniform output bits. -/
noncomputable def binaryLawE64 (F : FunEns) (h hp : HashFamily) (n k m : ℕ)
    (y : Bits) : ℝ :=
  lawOn (Finset.univ : Finset (Seed64 n k (h.keyLen n) (hp.keyLen n) ×
    (Fin m → Bool))) (fun z => encodeOut64 F h hp n k (outE64 F h hp n k m z.1 z.2)) y

/-- A concrete formulation of the false-entropy property for the repaired finite seed. -/
def IsFalseEntropy64 (F : FunEns) (h hp : HashFamily) (k : ℕ → ℕ) : Prop :=
  PTimeParam k ∧ IsPoly (m64 F k) ∧
  PolyParam (fun n => (m64 F k n : ℝ)) ∧
  (∃ M : Bits → Bits, PolyTimeComputable M ∧
    ∀ n, ∀ seed : Seed64 n (k n) (h.keyLen n) (hp.keyLen n),
      M (encAdvice n (m64 F k n) (encodeSeed64 seed)) =
        encodeOut64 F h hp n (k n) (outD64 F h hp n (k n) seed)) ∧
  (∃ M : Bits → Bits, PolyTimeComputable M ∧
    ∀ n, ∀ seed : Seed64 n (k n) (h.keyLen n) (hp.keyLen n),
    ∀ z : Fin (m64 F k n) → Bool,
      M (encAdvice n (m64 F k n) (encodeSeed64 seed ++ List.ofFn z)) =
        encodeOut64 F h hp n (k n)
          (outE64 F h hp n (k n) (m64 F k n) seed z)) ∧
  CompIndist (m64 F k) (fun n => outLen64 F h hp n (k n))
    (fun n => binaryLawD64 F h hp n (k n))
    (fun n => binaryLawE64 F h hp n (k n) (m64 F k n)) ∧
  ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n →
    entropyD64 F h hp n (k n) + 10 * (n : ℝ) ^ 2 ≤
      entropyE64 F h hp n (k n) (m64 F k n)

end HILL.PRG


