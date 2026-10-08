-- Prove2me | Definitions.Def_GOSNIZK_DLINCommit_Scheme
-- name    : GOSNIZK_DLINCommit_Scheme
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:11.575866+00:00
-- url     : https://prove2.me/theorems/c7a712d2-8b84-475e-be92-f4044fbb271a
-- title:
--   The decisional-linear homomorphic proof commitment of Figure 2: keys, com, Ext, Topen, P01 (corrected), V01, S01 (p. 12)
-- statement:
--   Fix a DLIN bilinear group $(p, \mathbb G, \mathbb G_T, e, g)$. Figure 2 of Groth, Ostrovsky and Sahai defines the following scheme.
--
--   1. **Keys.** For $x, y \in \mathbb Z_p^*$ and $r_u, s_v \in \mathbb Z_p$ put $f = g^x$, $h = g^y$. The *perfectly binding* generator $K_{\mathrm{binding}}$ also draws $z \in \mathbb Z_p^*$ and outputs the commitment key $ck = (f, h, u, v, w) = (f, h, f^{r_u}, h^{s_v}, g^{r_u+s_v+z})$ with extraction key $xk = (x, y, z)$. The *perfectly hiding* generator $K_{\mathrm{hiding}}$ outputs $ck = (f, h, f^{r_u}, h^{s_v}, g^{r_u+s_v})$ with trapdoor key $tk = (r_u, s_v)$. A key pair is *in the support* of a generator if it arises in this way for some admissible choices.
--   2. **Commitment.** Messages lie in $\mathbb Z_p$, randomizers in $\mathbb Z_p \times \mathbb Z_p$, commitments in $\mathbb G^3$ (with entry-wise multiplication):
--   $$\mathrm{com}(m; r, s) = (u^m f^r,\; v^m h^s,\; w^m g^{r+s}).$$
--   3. **Extraction.** $\mathrm{Ext}_{xk}(c_1, c_2, c_3)$ computes $d = c_3\, c_1^{-1/x}\, c_2^{-1/y}$ and returns the least $k \in \{0, \dots, p-1\}$ with $(g^z)^k = d$ (read in $\mathbb Z_p$), or $0$ if there is none.
--   4. **Trapdoor opening.** $\mathrm{Topen}_{tk}(m, (r, s), m') = (r - (m'-m)r_u,\; s - (m'-m)s_v)$.
--   5. **Proof that a commitment contains 0 or 1.** On an opening $(m, r, s)$ and proof randomness $t \in \mathbb Z_p$, $P_{01}$ returns $\pi = (\pi_{11}, \pi_{12}, \pi_{13}, \pi_{21}, \pi_{22}, \pi_{23}) \in \mathbb G^6$ with
--   $$\begin{aligned} \pi_{11} &= (u^{2m-1} f^r)^r, & \pi_{12} &= v^{(2m-1)r} h^{rs+t}, & \pi_{13} &= w^{(2m-1)r} g^{(r+s)r+t},\\ \pi_{21} &= u^{(2m-1)s} f^{rs-t}, & \pi_{22} &= (v^{2m-1} h^s)^s, & \pi_{23} &= w^{(2m-1)s} g^{(r+s)s-t}. \end{aligned}$$
--   6. **Verification.** With $\pi_{3j} = \pi_{1j}\pi_{2j}$, $V_{01}(ck, c, \pi)$ accepts iff
--   $$\begin{aligned} e(f, \pi_{11}) &= e(c_1, c_1u^{-1}), & e(f, \pi_{12})e(h, \pi_{21}) &= e(c_1, c_2v^{-1})e(c_2, c_1u^{-1}),\\ e(h, \pi_{22}) &= e(c_2, c_2v^{-1}), & e(f, \pi_{13})e(g, \pi_{31}) &= e(c_1, c_3w^{-1})e(c_3, c_1u^{-1}),\\ e(g, \pi_{33}) &= e(c_3, c_3w^{-1}), & e(h, \pi_{23})e(g, \pi_{32}) &= e(c_2, c_3w^{-1})e(c_3, c_2v^{-1}). \end{aligned}$$
--   7. **Randomness simulator.** $S_{01}(m, \rho_0, \rho_1, t)$, for a proof made with opening $(m, \rho_0)$ and randomness $t$ when $\rho_1$ opens the same commitment to $1-m$: for $m = 0$, $\rho_0 = (r_0, s_0)$, $\rho_1 = (r_1, s_1)$ it returns $t' = t + r_0 s_1 - s_0 r_1$; otherwise it returns the inverse map $t - r_1 s_0 + s_1 r_0$.
--
--   These objects are the decisional-linear instance of a homomorphic proof commitment; every theorem of the mission is about them.
--
--   **Formalization Note** *Erratum.* The paper prints $\pi_{12} = v^{(2m-1)r} h^{rs-t}$ and $\pi_{21} = u^{(2m-1)s} f^{rs+t}$. With those signs an honestly generated proof fails the fourth and sixth verification equations whenever $2t \ne 0$: the two sides differ by $e(g,g)^{2xt}$ and $e(g,g)^{-2yt}$. The definition uses the signs swapped in $\pi_{12}$ and $\pi_{21}$, which is the correction under which the paper's own argument for witness indistinguishability (p. 13, $t' = t + r_0 s_1 - s_0 r_1$) holds. Exponents in $\mathbb Z_p$ act through representatives in $\{0, \dots, p-1\}$. The paper's $xk = (ck, x, y, z)$ and $tk = (ck, r_u, s_v)$ are stored without the redundant $ck$. Acceptance of $V_{01}$ is a proposition. $S_{01}$ is read off the proof of Theorem 4 (p. 13); the paper only asserts that some polynomial-time simulator exists.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 12, Figure 2 (and p. 13, proof of Theorem 4, for S01)

import Mathlib
import Definitions.Def_GOSNIZK_DLINCommit_DLINSetup

namespace GOSNIZK.DLINCommit

/-- A commitment key `ck = (p, 𝔾, 𝔾_T, e, g, f, h, u, v, w)` of Figure 2 (Groth, Ostrovsky, Sahai 2012,
p. 12); the bilinear group part `(p, 𝔾, 𝔾_T, e, g)` is the `DLINSetup`, this structure holds the rest. -/
structure CommitKey (G : Type*) where
  f : G
  h : G
  u : G
  v : G
  w : G

/-- A proof `π = (π₁₁, π₁₂, π₁₃, π₂₁, π₂₂, π₂₃) ∈ 𝔾⁶` of the 0/1 proof of Figure 2. -/
structure Proof01 (G : Type*) where
  π11 : G
  π12 : G
  π13 : G
  π21 : G
  π22 : G
  π23 : G

namespace DLINSetup

variable {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
variable (S : DLINSetup G GT)

/-- The key produced by `K_binding` of Figure 2 (p. 12) on the random choices `x, y, z ∈ ℤ_p^*`,
`r_u, s_v ∈ ℤ_p`: `f = g^x`, `h = g^y`, `(u, v, w) = (f^{r_u}, h^{s_v}, g^{r_u + s_v + z})`. -/
def bindingKey (x y ru sv z : ZMod S.p) : CommitKey G :=
  { f := S.g ^ x.val, h := S.g ^ y.val, u := (S.g ^ x.val) ^ ru.val, v := (S.g ^ y.val) ^ sv.val,
    w := S.g ^ (ru + sv + z).val }

/-- The key produced by `K_hiding` of Figure 2 (p. 12) on the random choices `x, y ∈ ℤ_p^*`,
`r_u, s_v ∈ ℤ_p`: `f = g^x`, `h = g^y`, `(u, v, w) = (f^{r_u}, h^{s_v}, g^{r_u + s_v})`. -/
def hidingKey (x y ru sv : ZMod S.p) : CommitKey G :=
  { f := S.g ^ x.val, h := S.g ^ y.val, u := (S.g ^ x.val) ^ ru.val, v := (S.g ^ y.val) ^ sv.val,
    w := S.g ^ (ru + sv).val }

/-- `(ck, xk)` lies in the support of `K_binding` (Figure 2, p. 12): `xk = (x, y, z)` with
`x, y, z ∈ ℤ_p^*` (nonzero) and `ck = bindingKey x y r_u s_v z` for some `r_u, s_v ∈ ℤ_p`. (The paper's
`xk = (ck, x, y, z)`; the `ck` component is carried separately.) -/
def IsBindingKey (ck : CommitKey G) (xk : ZMod S.p × ZMod S.p × ZMod S.p) : Prop :=
  xk.1 ≠ 0 ∧ xk.2.1 ≠ 0 ∧ xk.2.2 ≠ 0 ∧
    ∃ ru sv : ZMod S.p, ck = S.bindingKey xk.1 xk.2.1 ru sv xk.2.2

/-- `(ck, tk)` lies in the support of `K_hiding` (Figure 2, p. 12): `tk = (r_u, s_v)` and
`ck = hidingKey x y r_u s_v` for some `x, y ∈ ℤ_p^*` (nonzero). (The paper's `tk = (ck, r_u, s_v)`.) -/
def IsHidingKey (ck : CommitKey G) (tk : ZMod S.p × ZMod S.p) : Prop :=
  ∃ x y : ZMod S.p, x ≠ 0 ∧ y ≠ 0 ∧ ck = S.hidingKey x y tk.1 tk.2

/-- The commitment `com(m; r, s) = (u^m f^r, v^m h^s, w^m g^{r+s}) ∈ 𝔾³` of Figure 2 (p. 12), with message
`m ∈ ℤ_p` and randomizer `(r, s) ∈ ℤ_p × ℤ_p`. `𝔾³` is the product group, so the group operation on
commitments is entry-wise multiplication. Exponents act through `a.val ∈ {0, …, p − 1}`. -/
def com (ck : CommitKey G) (m r s : ZMod S.p) : G × G × G :=
  (ck.u ^ m.val * ck.f ^ r.val, ck.v ^ m.val * ck.h ^ s.val, ck.w ^ m.val * S.g ^ (r + s).val)

/-- The extractor `Ext_xk(c)` of Figure 2 (p. 12), `xk = (x, y, z)`: compute
`d = c₃ c₁^{−1/x} c₂^{−1/y}` (which is `(g^z)^m`) and exhaustively search for `m`, i.e. return the least
`k < p` with `(g^z)^k = d`, read in `ℤ_p`; if there is none, return `0` (a failure value; this branch
never fires on a binding key). -/
noncomputable def Ext (xk : ZMod S.p × ZMod S.p × ZMod S.p) (c : G × G × G) : ZMod S.p := by
  classical
  exact
    if hc : ∃ k : ℕ, k < S.p ∧
        (S.g ^ xk.2.2.val) ^ k = c.2.2 * c.1 ^ (-1 / xk.1).val * c.2.1 ^ (-1 / xk.2.1).val then
      ((Nat.find hc : ℕ) : ZMod S.p)
    else 0

/-- The trapdoor opening `Topen_tk(m, (r, s), m′) = (r − (m′ − m) r_u, s − (m′ − m) s_v)` (mod `p`) of
Figure 2 (p. 12), `tk = (r_u, s_v)`. -/
def Topen (tk : ZMod S.p × ZMod S.p) (m : ZMod S.p) (rs : ZMod S.p × ZMod S.p) (m' : ZMod S.p) :
    ZMod S.p × ZMod S.p :=
  (rs.1 - (m' - m) * tk.1, rs.2 - (m' - m) * tk.2)

/-- The WI prover `P01(ck, m, (r, s); t)` of Figure 2 (p. 12), **with the signs of `t` in `π₁₂` and `π₂₁`
corrected**:
`π₁₁ = (u^{2m−1} f^r)^r`, `π₁₂ = v^{(2m−1)r} h^{rs+t}`, `π₁₃ = w^{(2m−1)r} g^{(r+s)r+t}`,
`π₂₁ = u^{(2m−1)s} f^{rs−t}`, `π₂₂ = (v^{2m−1} h^s)^s`, `π₂₃ = w^{(2m−1)s} g^{(r+s)s−t}`,
where `t ∈ ℤ_p` is the proof randomness (chosen uniformly by the prover).

Erratum: the paper prints `π₁₂ = v^{(2m−1)r} h^{rs−t}` and `π₂₁ = u^{(2m−1)s} f^{rs+t}`; with those signs
the honest proof fails the fourth and sixth verification equations whenever `2t ≠ 0` (the two sides differ
by `e(g, g)^{2xt}` and `e(g, g)^{−2yt}`, where `f = g^x`, `h = g^y`). The corrected signs are the ones under
which the paper's own witness-indistinguishability argument (p. 13, `t′ = t + r₀s₁ − s₀r₁`) holds. -/
def P01 (ck : CommitKey G) (m : ZMod S.p) (rs : ZMod S.p × ZMod S.p) (t : ZMod S.p) : Proof01 G :=
  { π11 := (ck.u ^ (2 * m - 1).val * ck.f ^ rs.1.val) ^ rs.1.val
    π12 := ck.v ^ ((2 * m - 1) * rs.1).val * ck.h ^ (rs.1 * rs.2 + t).val
    π13 := ck.w ^ ((2 * m - 1) * rs.1).val * S.g ^ ((rs.1 + rs.2) * rs.1 + t).val
    π21 := ck.u ^ ((2 * m - 1) * rs.2).val * ck.f ^ (rs.1 * rs.2 - t).val
    π22 := (ck.v ^ (2 * m - 1).val * ck.h ^ rs.2.val) ^ rs.2.val
    π23 := ck.w ^ ((2 * m - 1) * rs.2).val * S.g ^ ((rs.1 + rs.2) * rs.2 - t).val }

/-- The verifier `V01(ck, c, π)` of Figure 2 (p. 12): with `π₃ⱼ = π₁ⱼ π₂ⱼ` (`j = 1, 2, 3`), accept iff
the six pairing-product equations hold:
`e(f, π₁₁) = e(c₁, c₁u⁻¹)`, `e(f, π₁₂) e(h, π₂₁) = e(c₁, c₂v⁻¹) e(c₂, c₁u⁻¹)`,
`e(h, π₂₂) = e(c₂, c₂v⁻¹)`, `e(f, π₁₃) e(g, π₃₁) = e(c₁, c₃w⁻¹) e(c₃, c₁u⁻¹)`,
`e(g, π₃₃) = e(c₃, c₃w⁻¹)`, `e(h, π₂₃) e(g, π₃₂) = e(c₂, c₃w⁻¹) e(c₃, c₂v⁻¹)`.
Acceptance is a proposition (the verifier outputs 1 exactly when it holds). -/
def V01 (ck : CommitKey G) (c : G × G × G) (π : Proof01 G) : Prop :=
  S.e ck.f π.π11 = S.e c.1 (c.1 * ck.u⁻¹) ∧
  S.e ck.f π.π12 * S.e ck.h π.π21 = S.e c.1 (c.2.1 * ck.v⁻¹) * S.e c.2.1 (c.1 * ck.u⁻¹) ∧
  S.e ck.h π.π22 = S.e c.2.1 (c.2.1 * ck.v⁻¹) ∧
  S.e ck.f π.π13 * S.e S.g (π.π11 * π.π21) =
    S.e c.1 (c.2.2 * ck.w⁻¹) * S.e c.2.2 (c.1 * ck.u⁻¹) ∧
  S.e S.g (π.π13 * π.π23) = S.e c.2.2 (c.2.2 * ck.w⁻¹) ∧
  S.e ck.h π.π23 * S.e S.g (π.π12 * π.π22) =
    S.e c.2.1 (c.2.2 * ck.w⁻¹) * S.e c.2.2 (c.2.1 * ck.v⁻¹)

/-- The randomness simulator `S01(m, ρ₀, ρ₁, t)` read off the proof of Theorem 4 (p. 13). The proof `π` was
made with the opening `(m, ρ₀)` and randomness `t`; `ρ₁` is the opening of the same commitment to `1 − m`.
If `m = 0` (so `ρ₀ = (r₀, s₀)` opens to 0 and `ρ₁ = (r₁, s₁)` to 1) it returns `t′ = t + r₀s₁ − s₀r₁`;
otherwise (`ρ₀` opens to 1, `ρ₁` to 0) it returns the inverse map `t − r₁′s₀′ + s₁′r₀′` where
`ρ₁ = (r₁′, s₁′)`, `ρ₀ = (r₀′, s₀′)`. -/
def S01 (m : ZMod S.p) (ρ₀ ρ₁ : ZMod S.p × ZMod S.p) (t : ZMod S.p) : ZMod S.p :=
  if m = 0 then t + ρ₀.1 * ρ₁.2 - ρ₀.2 * ρ₁.1 else t - ρ₁.1 * ρ₀.2 + ρ₁.2 * ρ₀.1

end DLINSetup

end GOSNIZK.DLINCommit


