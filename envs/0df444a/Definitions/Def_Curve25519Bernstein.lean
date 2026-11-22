-- Prove2me | Definitions.Def_Curve25519Bernstein
-- name    : Curve25519Bernstein
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-22T17:13:05.913327+00:00
-- url     : https://prove2.me/theorems/9d84e77e-8eb9-4d3c-a9bc-2afa330773c0
-- title:
--   Curve25519, its group E(F_{p²}) and the x-coordinate ladder (Bernstein 2006)
-- statement:
--   The objects of Bernstein's *Curve25519: new Diffie-Hellman speed records* (2006). $\mathbf{F}_p$ is `ZMod p` for a prime $p$ (passed as an instance `Fact p.Prime`).
--
--   **The field $\mathbf{F}_{p^2}$.** `Fp2 p` is Mathlib's `GaloisField p 2`, the field with $p^2$ elements, and `emb p` is the inclusion $\mathbf{F}_p \to \mathbf{F}_{p^2}$. Appendix A (p. 19) builds $\mathbf{F}_{p^2}$ concretely: “Define $\mathbf{F}_{p^2}$ as the set $\mathbf{F}_p \times \mathbf{F}_p$. […] Define a binary operation $\cdot$ on $\mathbf{F}_{p^2}$ by $(a, b) \cdot (c, d) = (ac + \delta bd, ad + bc)$.” §2 says “Note that 2 is not a square in $\mathbf{F}_p$; define $\mathbf{F}_{p^2}$ as the field $(\mathbf{Z}/(2^{255} - 19))[\sqrt{2}]$.” (p. 4). Appendix A embeds $\mathbf{F}_p$: “The injection $a \mapsto (a, 0)$ from $\mathbf{F}_p$ to $\mathbf{F}_{p^2}$ is a ring morphism: it preserves $0, 1, -, +, \cdot$. Thus $(a, 0)$ is abbreviated $a$ without risk of confusion.” (p. 19). Any two fields with $p^2$ elements are isomorphic by an isomorphism fixing $\mathbf{F}_p$, and every statement of the mission is invariant under such an isomorphism, so the choice of model does not matter.
--
--   **The curve and $E(\mathbf{F}_{p^2})$ (Theorem 2.1, p. 4; Appendix A, p. 20).** “Define $E$ as the elliptic curve $y^2 = x^3 + Ax^2 + x$ over the field $\mathbf{F}_p$.” `curve p A` is the Weierstrass curve with $a_2 = A$, $a_4 = 1$ and $a_1 = a_3 = a_6 = 0$, `Ecurve p A` its base change to $\mathbf{F}_{p^2}$, and `Pt p A` Mathlib's group of its points: the point at infinity $\infty$ (`0`) and the nonsingular affine points, under the chord-and-tangent law. Appendix A: “Let $A$ be an integer such that $A^2 - 4 \bmod p$ is not a square in $\mathbf{F}_p$. Define $E(\mathbf{F}_{p^2})$ as $\{\infty\} \cup \{(x, y) \in \mathbf{F}_{p^2} : y^2 = x^3 + Ax^2 + x\}$.” (p. 20), with an explicit addition; a milestone shows that, when $A^2 - 4$ is not a square, every solution is a nonsingular point and Mathlib's operations satisfy the paper's formulas.
--
--   **$X_0$ and $X$ (§2, p. 4).** “Define a function $X_0 : E(\mathbf{F}_{p^2}) \to \mathbf{F}_{p^2}$ as follows: $X_0(\infty) = 0$; $X_0(x, y) = x$. Define a function $X : E(\mathbf{F}_{p^2}) \to \{\infty\} \cup \mathbf{F}_{p^2}$ as follows: $X(\infty) = \infty$; $X(x, y) = x$.” These are `X0` and `X`; `X` takes values in `Option (Fp2 p)`, with `none` for $\infty$.
--
--   **The quotient $x/z$ (Appendix B, p. 22).** “Here $x/z$ means the quotient of $x$ and $z$ in $\mathbf{F}_p$ if $z \neq 0$; it means $\infty$ if $x \neq 0$ and $z = 0$; it is undefined if $x = z = 0$.” `frac x z` is `none` ($\infty$) when $z = 0$ and $x/z$ otherwise; the statements using it assume $(x, z) \neq (0, 0)$.
--
--   **$\delta$ and two subsets (Appendix A, pp. 19–20).** “Find the smallest $\delta \in \{1, 2, \ldots, p - 1\}$ such that $\delta$ is not a square in $\mathbf{F}_p$.” This is `delta p` (an infimum, $0$ if there is no such $\delta$, which happens only for $p = 2$). Appendix A lists, among “the following three sets [that] are subgroups of $E(\mathbf{F}_{p^2})$”, the sets “$\{\infty\} \cup (E(\mathbf{F}_{p^2}) \cap (\mathbf{F}_p \times \mathbf{F}_p))$” and “$\{\infty\} \cup (E(\mathbf{F}_{p^2}) \cap (\mathbf{F}_p \times \sqrt{\delta}\mathbf{F}_p))$” (p. 20), where “The element $(0, 1)$ of $\mathbf{F}_{p^2}$ is abbreviated $\sqrt{\delta}$; it satisfies $\sqrt{\delta}^2 = (\delta, 0) = \delta$.” (p. 19). These are `fpPoints p A` and `twistPoints p A s`, the latter for a square root $s$ of $\delta$ in $\mathbf{F}_{p^2}$.
--
--   **The constants (§2, p. 4).** “In particular, define $p$ as the prime $2^{255} - 19$. […] Define $A = 486662$.” These are `p25519` and `A25519`.
--
--   **Keys and the Curve25519 function (§2, pp. 4–5).** “Write $s \mapsto \underline{s}$ for the standard little-endian bijection from $\{0, 1, \ldots, 2^{256} - 1\}$ to the set $\{0, 1, \ldots, 255\}^{32}$ of 32-byte strings: in other words, for each integer $s \in \{0, 1, \ldots, 2^{256} - 1\}$, define $\underline{s} = (s \bmod 256, \lfloor s/256 \rfloor \bmod 256, \ldots, \lfloor s/256^{31} \rfloor \bmod 256)$.” (p. 4): `bytes s` is $\underline{s}$ and `ofBytes` its inverse. “The set of Curve25519 public keys is, by definition, $\{0, 1, \ldots, 255\}^{32}$; in other words, $\{\underline{q} : q \in \{0, 1, \ldots, 2^{256} - 1\}\}$.” (p. 5): all of `Fin 32 → Fin 256`. “The set of Curve25519 secret keys is, by definition, $\{0, 8, 16, 24, \ldots, 248\} \times \{0, 1, \ldots, 255\}^{30} \times \{64, 65, 66, \ldots, 127\}$; in other words, $\{\underline{n} : n \in 2^{254} + 8\{0, 1, 2, 3, \ldots, 2^{251} - 1\}\}$.” These are `secretKeyBytes` and, on integers, `secretKeys`. “Now Curve25519 : {Curve25519 secret keys} × {Curve25519 public keys} → {Curve25519 public keys} is defined as follows. Fix $q \in \{0, 1, \ldots, 2^{256} - 1\}$ and $n \in 2^{254} + 8\{0, 1, 2, 3, \ldots, 2^{251} - 1\}$. By Theorem 2.1, there is a unique integer $s \in \{0, 1, 2, \ldots, 2^{255} - 20\}$ with the following property: $s = X_0(nQ)$ for all $Q \in E(\mathbf{F}_{p^2})$ such that $X_0(Q) = q \bmod 2^{255} - 19$. Finally, $\mathrm{Curve25519}(\underline{n}, \underline{q})$ is defined as $\underline{s}$.” (p. 5). `curve25519 n q` is the least $s \in \{0, 1, 2, \ldots, 2^{255} - 20\}$ with $s = X_0(nQ)$ for all $Q \in E(\mathbf{F}_{p^2})$ such that $X_0(Q) = q \bmod 2^{255} - 19$, and `curve25519Bytes` is the same function on 32-byte strings; that such an $s$ exists and is unique is a milestone, not part of the definition.
--
--   **The double-and-add procedure (§5, pp. 13–14).** `ladderStep a24 x₁ bit` acts on the fractions $(x, z)$ of $X(mQ)$ and $(x', z')$ of $X(mQ + Q)$, where $X(Q) = x_1/1$ and $a_{24} = (A - 2)/4$: on bit $0$ it returns the fractions of $X(2mQ)$ by Theorem B.1's formula and of $X(2mQ + Q)$ by Theorem B.2's formula with $z_1 = 1$; on bit $1$, those of $X((2m + 1)Q)$ by Theorem B.2 and of $X((2m + 2)Q)$ by Theorem B.1. `ladderIter a24 x₁ n k` applies it to bits $k - 1, \ldots, 0$ of $n$, most significant first. `ladder n q` is the Curve25519 computation of §5: “I compute $X(nQ)$ for any $n \in 2^{254} + 8\{0, 1, \ldots, 2^{251} - 1\}$ with 255 doublings and 255 additions starting from $X(Q), X(0), X(Q)$” and then “$X_0(nQ) = xz^{p-2}$”, with $a_{24} = 121665$ and starting fractions $X(0) = 1/0$, $X(Q) = q/1$.
-- source:
--   Bernstein, D. J., Curve25519: new Diffie-Hellman speed records, in: Public Key Cryptography – PKC 2006, Lecture Notes in Computer Science 3958, Springer, 2006, 207–228, https://doi.org/10.1007/11745853_14 (author's version of 2006-02-09: https://cr.yp.to/ecdh/curve25519-20060209.pdf), pp. 4–5, the curve y² = x³ + Ax² + x and E(F_{p²}) (Theorem 2.1, p. 4; Appendix A, pp. 19–20), X₀ and X (§2, p. 4), x/z (Appendix B, p. 22), δ and the subsets of Appendix A (pp. 19–20), p = 2^255 − 19 and A = 486662 (§2, p. 4), the secret keys, the byte encoding and the Curve25519 function (§2, pp. 4–5), and the double-and-add procedure (§5, pp. 13–14)

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Curve25519 (Bernstein 2006)

Definitions from D. J. Bernstein, *Curve25519: new Diffie-Hellman speed records* (PKC 2006):
the curve `y² = x³ + Ax² + x` over `F_p` and its points over `F_{p²}` (Theorem 2.1, Appendix A),
the x-coordinate maps `X₀` and `X` (§2), the quotient `x/z` of Appendix B, the smallest
non-square `δ` and the two subsets of Appendix A, the constants of §2, the secret keys and the
Curve25519 function on integers (§2), the little-endian byte encoding (§2), and the
double-and-add procedure of §5.
-/

noncomputable section

namespace Bernstein

open WeierstrassCurve

/-- The curve `y² = x³ + Ax² + x` over `F_p = ZMod p` (Theorem 2.1, p. 4). -/
def curve (p : ℕ) (A : ℤ) : WeierstrassCurve (ZMod p) where
  a₁ := 0
  a₂ := A
  a₃ := 0
  a₄ := 1
  a₆ := 0

/-- The field `F_{p²}`, taken as Mathlib's `GaloisField p 2`. -/
abbrev Fp2 (p : ℕ) [Fact p.Prime] : Type := GaloisField p 2

/-- Equality in `F_{p²}` is decided classically; the group law on `E(F_{p²})` needs a decision
procedure. -/
instance (p : ℕ) [Fact p.Prime] : DecidableEq (Fp2 p) := Classical.decEq _

/-- The embedding `F_p → F_{p²}`. -/
abbrev emb (p : ℕ) [Fact p.Prime] : ZMod p →+* Fp2 p := algebraMap (ZMod p) (Fp2 p)

/-- The curve `y² = x³ + Ax² + x` with coefficients in `F_{p²}`, in affine coordinates. -/
abbrev Ecurve (p : ℕ) [Fact p.Prime] (A : ℤ) : Affine (Fp2 p) :=
  ((curve p A).baseChange (Fp2 p)).toAffine

/-- The group `E(F_{p²})`: the point at infinity and the nonsingular affine points of the curve
with coordinates in `F_{p²}`, under the chord-and-tangent law. -/
abbrev Pt (p : ℕ) [Fact p.Prime] (A : ℤ) : Type := (Ecurve p A).Point

/-- The prime `2^255 − 19` (§2, p. 4). -/
def p25519 : ℕ := 2 ^ 255 - 19

/-! ## The double-and-add procedure of §5 -/

section Ladder

variable {p : ℕ}


/-- One step of §5's scalar multiplication on the fractions `(x, z)` for `X(mQ)` and `(x', z')`
for `X(mQ + Q)`, with `a24 = (A − 2)/4` and `X(Q) = x₁/1`. On bit `0` it returns the fractions
of `X(2mQ) = X(2(mQ))` (Theorem B.1) and `X(2mQ + Q) = X((mQ + Q) + mQ)` (Theorem B.2 with
`z₁ = 1`); on bit `1` those of `X((2m + 1)Q) = X((mQ + Q) + mQ)` and
`X((2m + 1)Q + Q) = X(2(mQ + Q))`. -/
def ladderStep (a24 x₁ : ZMod p) (bit : Bool) (st : ZMod p × ZMod p × ZMod p × ZMod p) :
    ZMod p × ZMod p × ZMod p × ZMod p :=
  let dbl : ZMod p × ZMod p → ZMod p × ZMod p := fun (x, z) =>
    ((x + z) ^ 2 * (x - z) ^ 2,
      ((x + z) ^ 2 - (x - z) ^ 2) * ((x + z) ^ 2 + a24 * ((x + z) ^ 2 - (x - z) ^ 2)))
  let add : ZMod p × ZMod p → ZMod p × ZMod p → ZMod p × ZMod p := fun (x, z) (x', z') =>
    (((x - z) * (x' + z') + (x + z) * (x' - z')) ^ 2,
      ((x - z) * (x' + z') - (x + z) * (x' - z')) ^ 2 * x₁)
  let (x, z, x', z') := st
  if bit then
    let s := add (x', z') (x, z)
    let d := dbl (x', z')
    (s.1, s.2, d.1, d.2)
  else
    let d := dbl (x, z)
    let s := add (x', z') (x, z)
    (d.1, d.2, s.1, s.2)

/-- §5's formulas repeated `k` times: bits `k − 1, …, 1, 0` of `n` are processed, most
significant first, starting from the state `st`. -/
def ladderIter (a24 x₁ : ZMod p) (n : ℕ) : ℕ → ZMod p × ZMod p × ZMod p × ZMod p →
    ZMod p × ZMod p × ZMod p × ZMod p
  | 0, st => st
  | k + 1, st => ladderIter a24 x₁ n k (ladderStep a24 x₁ (n.testBit k) st)

/-- §5's computation of `X₀(nQ)` from `q = X₀(Q)` on Curve25519: 255 doublings and 255 additions
starting from `X(Q) = q/1`, `X(0) = 1/0`, `X(Q) = q/1`, then `X₀(nQ) = x z^{p−2}` for the
final fraction `x/z` of `X(nQ)`. -/
def ladder (n : ℕ) (q : ZMod p25519) : ZMod p25519 :=
  let st := ladderIter (121665 : ZMod p25519) q n 255 (1, 0, q, 1)
  st.1 * st.2.1 ^ (p25519 - 2)

end Ladder

variable {p : ℕ} [Fact p.Prime] {A : ℤ}

/-- `X₀ : E(F_{p²}) → F_{p²}`, with `X₀(∞) = 0` and `X₀(x, y) = x` (§2). -/
def X0 : Pt p A → Fp2 p
  | .zero => 0
  | .some x _ _ => x

/-- `X : E(F_{p²}) → {∞} ∪ F_{p²}`, with `X(∞) = ∞` (here `none`) and `X(x, y) = x` (§2). -/
def X : Pt p A → Option (Fp2 p)
  | .zero => none
  | .some x _ _ => some x

/-- The quotient `x/z` of Appendix B (p. 22) for `x, z ∈ F_p`, as an element of
`{∞} ∪ F_{p²}`: `x/z` if `z ≠ 0`, and `∞` (here `none`) if `z = 0`. -/
def frac (x z : ZMod p) : Option (Fp2 p) :=
  if z = 0 then none else some (emb p (x / z))

/-- The smallest `δ ∈ {1, 2, …, p − 1}` that is not a square in `F_p` (Appendix A, p. 19). -/
noncomputable def delta (p : ℕ) : ℕ :=
  sInf {d : ℕ | 1 ≤ d ∧ d < p ∧ ¬ IsSquare (d : ZMod p)}

variable (p A) in
/-- `{∞} ∪ (E(F_{p²}) ∩ (F_p × F_p))` (Appendix A, p. 20). -/
def fpPoints : Set (Pt p A) :=
  {Q | Q = 0 ∨ ∃ (x y : ZMod p) (h : _), Q = .some (emb p x) (emb p y) h}

variable (p A) in
/-- `{∞} ∪ (E(F_{p²}) ∩ (F_p × √δ F_p))` (Appendix A, p. 20), for a square root `s` of `δ`
in `F_{p²}`. -/
def twistPoints (s : Fp2 p) : Set (Pt p A) :=
  {Q | Q = 0 ∨ ∃ (x c : ZMod p) (h : _), Q = .some (emb p x) (s * emb p c) h}


/-- `A = 486662` (§2, p. 4). -/
def A25519 : ℤ := 486662

/-- The Curve25519 secret keys as integers: `n ∈ 2^254 + 8{0, 1, 2, 3, …, 2^251 − 1}`
(§2, p. 5). -/
def secretKeys : Set ℕ := {n | ∃ i < 2 ^ 251, n = 2 ^ 254 + 8 * i}

/-- The standard little-endian bijection `s ↦ s̲` from `{0, 1, …, 2^256 − 1}` to 32-byte strings:
`s̲ = (s mod 256, ⌊s/256⌋ mod 256, …, ⌊s/256^31⌋ mod 256)` (§2, p. 4). -/
def bytes (s : ℕ) : Fin 32 → Fin 256 :=
  fun i => ⟨s / 256 ^ (i : ℕ) % 256, Nat.mod_lt _ (by norm_num)⟩

/-- The integer `∑ᵢ bᵢ 256^i` encoded by a 32-byte string `b`, little-endian (§2, p. 4). -/
def ofBytes (b : Fin 32 → Fin 256) : ℕ :=
  ∑ i : Fin 32, (b i : ℕ) * 256 ^ (i : ℕ)

/-- The Curve25519 secret keys as byte strings:
`{0, 8, 16, 24, …, 248} × {0, 1, …, 255}^30 × {64, 65, 66, …, 127}` (§2, p. 5). -/
def secretKeyBytes : Set (Fin 32 → Fin 256) :=
  {b | (b 0 : ℕ) % 8 = 0 ∧ 64 ≤ (b 31 : ℕ) ∧ (b 31 : ℕ) ≤ 127}

/-- `Curve25519(n, q)` on integers (§2, p. 5): the least `s ∈ {0, 1, 2, …, 2^255 − 20}` with
`s = X₀(nQ)` for all `Q ∈ E(F_{p²})` such that `X₀(Q) = q mod 2^255 − 19`. -/
noncomputable def curve25519 [Fact p25519.Prime] (n q : ℕ) : ℕ :=
  sInf {s : ℕ | s ≤ 2 ^ 255 - 20 ∧
    ∀ Q : Pt p25519 A25519, X0 Q = emb p25519 (q : ZMod p25519) →
      X0 ((n : ℤ) • Q) = emb p25519 (s : ZMod p25519)}

/-- `Curve25519 : {secret keys} × {public keys} → {public keys}` on 32-byte strings (§2, p. 5):
`Curve25519(n̲, q̲) = s̲` for `s = Curve25519(n, q)` on integers. -/
noncomputable def curve25519Bytes [Fact p25519.Prime] (n q : Fin 32 → Fin 256) :
    Fin 32 → Fin 256 :=
  bytes (curve25519 (ofBytes n) (ofBytes q))

end Bernstein

end


