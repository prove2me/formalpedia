-- Prove2me | Definitions.Def_NOFSeparation750_CodedGIP_Model
-- name    : NOFSeparation750_CodedGIP_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:42:11.147202+00:00
-- url     : https://prove2.me/theorems/166c2755-8e8c-40e5-8b5a-d4b72c8b515a
-- title:
--   Total coded GIP, basis decoding, and padding to all lengths
-- statement:
--   A forehead is a tuple of $\ell$ words of a small code $V$ and one word of a large code $W$. The total Boolean function is
--   $$\operatorname{CodedGIP}(x)=1\quad\Longleftrightarrow\quad\sum_{h=1}^{\ell}\bigodot_{i=1}^{k}a_h^{(i)}=\sum_{i=1}^{k}c^{(i)}$$
--   as equality of entire vectors. Fixed ordered bases and a bijection between $b$-bit strings and field elements decode consecutive groups of bits into basis coefficients. Thus every native string of length $n_j=(\ell m_j+\widetilde m_j)b$ represents exactly one forehead, without a promise or invalid-input branch.
--
--   Write $q=4^a$, $s=2^a$, $b=2a$, $r_j=(4^a-2^a)(2^a)^j$, and $\ell=2^{k+2}k$. Allowed parameters satisfy $a\ge1$ and $(32k)^2\le4^a\le(64k)^2$. For arbitrary length $n$, set $U_j=(\ell+1)r_jb$. Below $U_0$ the padded function is constantly zero. Otherwise select the largest $j$ with $U_j\le n$, use the first $n_j$ bits of each block, and ignore the tail. A finite search through $j\le n$ selects this level; allowed parameters guarantee that this range contains every eligible level.
--
--   The structural definitions also give total values at other parameters. All construction claims use allowed parameters. Basis dimensions are at most $r_j$, so $n_j\le U_j$; the rate bound yields $n_j=\Theta_k(n)$ at the selected levels. This is an explicit choice for the source's standard-padding convention.
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), §2, p.6; §3, p.7, Definition 3.3 and standard-padding sentence; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Programs
import Definitions.Def_NOFSeparation750_CodedGIP_Codes
import Definitions.Def_NOFSeparation750_CodedGIP_Protocols

noncomputable section

namespace NOFSeparation750.CodedGIP
attribute [local instance] Classical.propDecidable

/-- Every structured forehead is a tuple of actual codewords. -/
abbrev Forehead {F : Type} [Field F] {r : ℕ} (D : CodePair F r) (ℓ : ℕ) :=
  (Fin ℓ → D.small.code) × D.large.code

/-- Definition 3.3: equality of whole vectors, not one coordinate or its sum. -/
def codedGIP {F : Type} [Field F] {r : ℕ} (D : CodePair F r) (ℓ k : ℕ)
    (x : Fin k → Forehead D ℓ) : Bool :=
  decide ((∑ h : Fin ℓ, (fun t => ∏ i : Fin k, ((x i).1 h).val t)) =
    ∑ i : Fin k, (x i).2.val)

def nativeLength {F : Type} [Field F] {r : ℕ} (D : CodePair F r) (ℓ b : ℕ) : ℕ :=
  (ℓ * D.small.dimension + D.large.dimension) * b

/-- Consecutive b-bit groups, decoded through the fixed field bijection and the
specified bases. All accesses are within nativeLength on native inputs. -/
def decodeForehead {F : Type} [Field F] {r b : ℕ} (D : CodePair F r)
    (codec : (Fin b → Bool) ≃ F) (ℓ : ℕ) (x : Fin (nativeLength D ℓ b) → Bool) : Forehead D ℓ :=
  let bits := List.ofFn x
  (fun h => D.small.encode (fun a => codec (fun t =>
      bits.getD ((h.val * D.small.dimension + a.val) * b + t.val) false)),
    D.large.encode (fun a => codec (fun t =>
      bits.getD ((ℓ * D.small.dimension + a.val) * b + t.val) false)))

def nativeFunction {F : Type} [Field F] {r b : ℕ} (D : CodePair F r)
    (codec : (Fin b → Bool) ≃ F) (ℓ k : ℕ)
    (x : Fin k → Bits (nativeLength D ℓ b)) : Bool :=
  codedGIP D ℓ k (fun i => decodeForehead D codec ℓ (x i))

def copies (k : ℕ) : ℕ := 2 ^ (k + 2) * k
/-- q = 4^a, s = 2^a, b = 2a: no real square root or fractional Nat power. -/
def codeLength (a j : ℕ) : ℕ := (4 ^ a - 2 ^ a) * (2 ^ a) ^ j

def Allowed (k a : ℕ) : Prop :=
  1 ≤ a ∧ (32 * k) ^ 2 ≤ 4 ^ a ∧ 4 ^ a ≤ (64 * k) ^ 2

abbrev PairFamily (F : Type) [Field F] (a : ℕ) := (j : ℕ) → CodePair F (codeLength a j)

def envelope (k a j : ℕ) : ℕ := (copies k + 1) * codeLength a j * (2 * a)

/-- Bounded finite search for the largest level with U_j ≤ n. For allowed
parameters U_j grows geometrically and j ≤ n includes every eligible level. -/
def paddingLevel (k a n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun j => envelope k a j ≤ n)).max.getD 0

/-- All lengths, including zero. Prefix padding below a native length is total
(getD=false); with allowed parameters and basis dimensions no such access occurs.
Below U_0 the function is constantly false. -/
def paddedFamily {F : Type} [Field F] {a : ℕ} (D : PairFamily F a)
    (codec : (Fin (2 * a) → Bool) ≃ F) (k : ℕ) : BooleanFamily k :=
  fun n x => if n < envelope k a 0 then false else
    let j := paddingLevel k a n
    nativeFunction (D j) codec (copies k) k (fun i t => (List.ofFn (x i)).getD t.val false)

end NOFSeparation750.CodedGIP


