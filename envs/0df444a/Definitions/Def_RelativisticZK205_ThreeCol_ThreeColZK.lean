-- Prove2me | Definitions.Def_RelativisticZK205_ThreeCol_ThreeColZK
-- name    : RelativisticZK205_ThreeCol_ThreeColZK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:08:09.512475+00:00
-- url     : https://prove2.me/theorems/76a4a2c9-9ea5-4322-ba70-955be8020f20
-- title:
--   The 3-COLZK channel of Fig. 10
-- statement:
--   The **3-COLZK** channel takes from Alice the bits $z_{00},z_{01},z_{10},z_{11}$ and $r$, and from Bob the bits $z'_{00},z'_{01},z'_{10},z'_{11}$ and $r'$; Alice receives $(\ell_0,\ell_1)\in\mathbb Z_3^2$ and Bob $(\ell'_0,\ell'_1)\in\mathbb Z_3^2$. Write $m_{uv}=z_{uv}\oplus z'_{uv}$ for $u,v\in\{0,1\}$, and $\bar u=1-u$.
--
--   If the inputs satisfy the condition that each vertex matches at most one vertex on the other side,
--
--   $$
--   m_{uv}\,m_{u\bar v}=m_{uv}\,m_{\bar uv}=0\quad\text{for all }u,v\in\{0,1\},
--   $$
--
--   the channel samples $(\ell_0,\ell_1,\ell'_0,\ell'_1)\in\mathbb Z_3^4$ uniformly among the solutions of the constraints, for all $u,v$:
--
--   1. $\ell_u=\ell'_v$ if $r\oplus r'=0$ and $m_{uv}=1$;
--   2. $\ell_u+\ell'_v\not\equiv\ell_{\bar u}+\ell'_{\bar v}\pmod 3$ if $r\oplus r'=1$, $m_{uv}=1$ and $m_{\bar u\bar v}=1$.
--
--   Otherwise it samples uniformly from $\mathbb Z_3^4$. The solution set is never empty.
--
--   3-COLZK is the fixed-size channel through which the simulators of §5.1 produce their answers, once each has compressed its query into four comparison bits.
--
--   **Formalization Note** Indices $u,v\in\{0,1\}$ are `Bool` (`false` $=0$), so $\bar u$ is `!u`; a party's input is the table `Bool → Bool → Bool` with its bit $r$, and its output is a pair in `ZMod 3 × ZMod 3`, whose component $\ell_u$ is `sel l u`. The channel is defined on all $2^{10}$ input pairs as two-party inputs, not on $m$ and $r\oplus r'$ alone. Nonemptiness of the solution set is proved in the file with the witnesses $(0,0,0,0)$ for $r\oplus r'=0$ and $(0,1,0,0)$ for $r\oplus r'=1$, so `PMF.uniformOfFinset` needs no fallback.
-- source:
--   Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, Relativistic Zero Knowledge, STOC 2027 submission #205 (October 2026), p.11, Fig. 10

import Mathlib
import Definitions.Def_RelativisticZK205_ThreeCol_Channel

/-!
# The 3-COLZK channel

Claude Crépeau, Harmanpreet Singh Grover, April Niu, Nan Yang, Fadi Younes, *Relativistic Zero
Knowledge*, STOC 2027 submission #205 (October 2026), p.11, Fig. 10.

Indices `u, v ∈ {0, 1}` are encoded as `Bool` (`false = 0`, `true = 1`), so `ū = !u`.
-/

namespace RelativisticZK205.ThreeCol

/-- One party's input to 3-COLZK: the four bits `z_uv` (as a function of `u, v`) and the bit `r`. -/
abbrev ColzkIn : Type := (Bool → Bool → Bool) × Bool

/-- One party's output of 3-COLZK: `(ℓ₀, ℓ₁) ∈ ℤ₃²`. -/
abbrev ColzkOut : Type := ZMod 3 × ZMod 3

/-- The component `ℓ_u` of an output pair `(ℓ₀, ℓ₁)`. -/
def sel (l : ColzkOut) (u : Bool) : ZMod 3 := if u then l.2 else l.1

/-- Fig. 10, p.11: the condition "each vertex matches at most one vertex on the other side",
`∀ u v, m_uv · m_uv̄ = m_uv · m_ūv = 0`, where `m_uv = z_uv ⊕ z'_uv`. -/
def ValidPattern (m : Bool → Bool → Bool) : Prop :=
  ∀ u v : Bool, (m u v && m u (!v)) = false ∧ (m u v && m (!u) v) = false

instance (m : Bool → Bool → Bool) : Decidable (ValidPattern m) := by
  unfold ValidPattern; infer_instance

/-- Fig. 10, p.11: the constraints of 3-COLZK on `(ℓ₀, ℓ₁, ℓ'₀, ℓ'₁)`, for the pattern `m` and
`s = r ⊕ r'`: for all `u, v`,
* `ℓ_u = ℓ'_v` if `s = 0` and `m_uv = 1`;
* `ℓ_u + ℓ'_v ≢ ℓ_ū + ℓ'_v̄ (mod 3)` if `s = 1`, `m_uv = 1` and `m_ūv̄ = 1`. -/
def ColzkConstraint (m : Bool → Bool → Bool) (s : Bool) (l l' : ColzkOut) : Prop :=
  ∀ u v : Bool,
    (s = false → m u v = true → sel l u = sel l' v) ∧
    (s = true → m u v = true → m (!u) (!v) = true →
      sel l u + sel l' v ≠ sel l (!u) + sel l' (!v))

instance (m : Bool → Bool → Bool) (s : Bool) (l l' : ColzkOut) :
    Decidable (ColzkConstraint m s l l') := by
  unfold ColzkConstraint; infer_instance

/-- The solution set of the 3-COLZK constraints. -/
def colzkSolutions (m : Bool → Bool → Bool) (s : Bool) : Finset (ColzkOut × ColzkOut) :=
  Finset.univ.filter fun p => ColzkConstraint m s p.1 p.2

/-- The solution set is never empty: `(0,0,0,0)` solves it when `s = 0` and `(0,1,0,0)` when
`s = 1`. -/
lemma colzkSolutions_nonempty (m : Bool → Bool → Bool) (s : Bool) :
    (colzkSolutions m s).Nonempty := by
  cases s
  · refine ⟨((0, 0), (0, 0)), ?_⟩
    simp only [colzkSolutions, Finset.mem_filter, Finset.mem_univ, true_and, ColzkConstraint]
    intro u v
    cases u <;> cases v <;> simp [sel]
  · refine ⟨((0, 1), (0, 0)), ?_⟩
    simp only [colzkSolutions, Finset.mem_filter, Finset.mem_univ, true_and, ColzkConstraint]
    intro u v
    cases u <;> cases v <;> simp [sel]

/-- Fig. 10, p.11: the 3-COLZK channel. Alice inputs `(z₀₀, z₀₁, z₁₀, z₁₁, r)`, Bob inputs
`(z'₀₀, z'₀₁, z'₁₀, z'₁₁, r')`; Alice receives `(ℓ₀, ℓ₁)` and Bob `(ℓ'₀, ℓ'₁)` in `ℤ₃²`. With
`m_uv = z_uv ⊕ z'_uv`: if the pattern `m` satisfies the condition `ValidPattern`, the output is
uniform among the solutions of `ColzkConstraint m (r ⊕ r')`; otherwise it is uniform on `ℤ₃⁴`. -/
noncomputable def threeColZK : Channel ColzkIn ColzkIn ColzkOut ColzkOut := fun a b =>
  let m : Bool → Bool → Bool := fun u v => xor (a.1 u v) (b.1 u v)
  let s : Bool := xor a.2 b.2
  if ValidPattern m then
    PMF.uniformOfFinset (colzkSolutions m s) (colzkSolutions_nonempty m s)
  else
    PMF.uniformOfFintype (ColzkOut × ColzkOut)

end RelativisticZK205.ThreeCol


