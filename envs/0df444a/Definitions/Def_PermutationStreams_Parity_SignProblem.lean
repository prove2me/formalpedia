-- Prove2me | Definitions.Def_PermutationStreams_Parity_SignProblem
-- name    : PermutationStreams_Parity_SignProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:26.621629+00:00
-- url     : https://prove2.me/theorems/4338dc14-fb08-48da-ad51-b19d02ae0f4b
-- title:
--   The product of local permutation signs and the block permutation
-- statement:
--   Write $[3]=\{1,2,3\}$. A triple $(a,b,c)\in[3]^3$ is **promised** when it is a permutation of $(1,2,3)$. Let $\mu$ be the uniform distribution on the six promised triples, and on them put
--
--   $$
--   \varepsilon(a,b,c)=\operatorname{sgn}(a,b,c)=(-1)^{\operatorname{inv}(a,b,c)} .
--   $$
--
--   For $x,y,z\in[3]^m$ whose coordinate triples are all promised,
--
--   $$
--   f_m(x,y,z)=\prod_{i=1}^m \varepsilon(x_i,y_i,z_i)\in\{-1,+1\}.
--   $$
--
--   For $\alpha\in\mathbb R$, the **sign correlation bound with constant $\alpha$** is the assertion of Lemma 4.3: for all $m\ge1$ and all $F,G,H:[3]^m\to D$,
--
--   $$
--   \Bigl|\ \mathbb E_{\mu^{\otimes m}}\bigl[f_m(x,y,z)\,F(x)\,G(y)\,H(z)\bigr]\Bigr|\le 2^{-\alpha m}.
--   $$
--
--   Finally, for a promised input the **block permutation** is the concatenation $\pi=A(x)B(y)C(z)$ of
--
--   $$
--   A(x)=(3(i-1)+x_i)_{i=1}^m,\quad B(y)=(3(i-1)+y_i)_{i=1}^m,\quad C(z)=(3(i-1)+z_i)_{i=1}^m ,
--   $$
--
--   a permutation of $[3m]$ with three increasing blocks, each of which a single player can write down from its own input.
--
--   These objects carry the three-party problem of §4.2 and the reduction of §4.3.
--
--   **Formalization Note** $[3]$ is encoded as $\{0,1,2\}$ and coordinates are $0$-based, so position $k\in\{0,\dots,3m-1\}$ of the block permutation lies in block $\lfloor k/m\rfloor$ (Alice, Bob, Charlie) at coordinate $i=k\bmod m$ and carries the value $3i+w_i$, one less than the paper's value; comparisons are unchanged. $\varepsilon$ and $f_m$ are defined on all triples by the same formula; only their values on promised triples are used, and $\mu$ gives the others probability zero. The correlation is computed with $f_m\in\{\pm1\}$ viewed as a complex number.
--
--   Differences from the source:
--   - encoding: [3] = {1,2,3}, coordinates 1,…,m, values 3(i−1)+x_i → Fin 3 = {0,1,2}, coordinates Fin m, values 3i + x_i in ℕ; reason: an order-preserving shift by one
--   - encoding: ε defined on the six permutations → ε defined on all of [3]^3 by the same formula; reason: the extra values have probability zero and the promise is a hypothesis wherever it matters
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §4.2, p. 6 (µ, ε, f_m, Lemma 4.3 inequality); §4.3, p. 7 (A(x), B(y), C(z), π)

import Definitions.Def_PermutationStreams_Parity_Inversions
import Definitions.Def_PermutationStreams_Parity_Correlation

namespace PermutationStreams.Parity

/-- `[3]` is encoded as `Fin 3 = {0, 1, 2}` (value `j` stands for `j + 1`). A triple is
promised when it is a permutation of `(1, 2, 3)`, i.e. its entries are pairwise distinct. -/
def IsPermTriple (t : Fin 3 × Fin 3 × Fin 3) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

instance (t : Fin 3 × Fin 3 × Fin 3) : Decidable (IsPermTriple t) := by
  unfold IsPermTriple; infer_instance

/-- §4.2 p.6: the uniform law on the six permutations of `(1, 2, 3)`. -/
noncomputable def mu6 (t : Fin 3 × Fin 3 × Fin 3) : ℝ :=
  if IsPermTriple t then 1 / 6 else 0

/-- The triple `(a, b, c)` as a length-three sequence. -/
def tripleSeq (t : Fin 3 × Fin 3 × Fin 3) : Fin 3 → Fin 3 :=
  ![t.1, t.2.1, t.2.2]

/-- `ε(a, b, c) = sgn(a, b, c) = (-1)^{inv(a,b,c)}` (p.6), defined on every triple; only its
values on promised triples are used. -/
def eps (t : Fin 3 × Fin 3 × Fin 3) : ℤˣ :=
  sgnSeq (tripleSeq t)

/-- `f_m(x, y, z) = ∏_{i=1}^m ε(x_i, y_i, z_i)` (p.6), with coordinates `Fin m`. -/
def fm (m : ℕ) (x y z : Fin m → Fin 3) : ℤˣ :=
  ∏ i, eps (x i, y i, z i)

/-- The promise of §4.2 p.7: every coordinate triple is a permutation of `[3]`. -/
def Promised (m : ℕ) (x y z : Fin m → Fin 3) : Prop :=
  ∀ i, IsPermTriple (x i, y i, z i)

/-- The correlation bound of Lemma 4.3 with constant `α`: for all `m ≥ 1` and all
`F, G, H : [3]^m → D`, `|E_{μ^{⊗m}}[f_m(x,y,z) F(x) G(y) H(z)]| ≤ 2^{-αm}`. -/
def SignCorrelationBound (α : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ F G H : (Fin m → Fin 3) → ℂ,
    (∀ x, ‖F x‖ ≤ 1) → (∀ y, ‖G y‖ ≤ 1) → (∀ z, ‖H z‖ ≤ 1) →
    ‖prodExpect mu6 m (fun w =>
        (((fm m (fun i => (w i).1) (fun i => (w i).2.1) (fun i => (w i).2.2) : ℤˣ) : ℤ) : ℂ) *
        F (fun i => (w i).1) * G (fun i => (w i).2.1) * H (fun i => (w i).2.2))‖
      ≤ (2 : ℝ) ^ (-(α * m))

/-- §4.3 p.7: the concatenation `π = A(x) B(y) C(z)` with `A(x) = (3(i-1) + x_i)_{i=1}^m`
and likewise `B(y)`, `C(z)`. In the 0-based encoding, position `k ∈ {0, …, 3m-1}` lies in block
`⌊k/m⌋` (0 = Alice, 1 = Bob, 2 = Charlie) at coordinate `i = k mod m` and carries the value
`3i + w_i ∈ {0, …, 3m-1}`, each value one less than the paper's. -/
def blockStream (m : ℕ) (x y z : Fin m → Fin 3) (k : Fin (3 * m)) : ℕ :=
  have hm : 0 < m := by have := k.isLt; omega
  let i : Fin m := ⟨k.val % m, Nat.mod_lt _ hm⟩
  3 * i.val + (if k.val / m = 0 then x i else if k.val / m = 1 then y i else z i).val

end PermutationStreams.Parity


