-- Prove2me | Definitions.Def_BianchiIX_AxisAndOrbitData
-- name    : BianchiIX_AxisAndOrbitData
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-06T03:29:34.011991+00:00
-- url     : https://prove2.me/theorems/d047df8e-5b45-48de-ab04-753697511ba3
-- title:
--   Physical axis charts, core flight times and the Brehm attractor input
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Let $X=\mathbb R^5$ with coordinates $x=(p,s,a,b,c)$ and the sup norm. Write
--   $$F(x)=(P,Q,r_1a,r_2b,r_3c),\qquad \mathcal C(x)=C(p,s,a,b,c),$$
--   and let $W=\{(p,s,a,b,c)\in X:a>0,\ b>0,\ c>0\}$.
--
--   Write $N_1(x)=a$, $N_2(x)=b$, and $N_3(x)=c$. For initial data $(x_0,t_0)$,
--   let $I_{\max}(x_0,t_0)$ be the union of all open convex domains of solutions
--   with these initial data, and let $\alpha_{x_0,t_0}$ be their compatible curve.
--   A solution $S$ has such a domain $I_S$, a curve $\alpha_S$, and
--   $\alpha_S(t_0)=x_0$.
--
--   Let $\mathcal L(X,X)$ be the continuous linear operators on $X$ and set
--   $$A(x)=dF_x,\qquad \widetilde F(x,J)=(F(x),A(x)\circ J).$$
--
--   For a fixed initial time $t_0$, put
--   $$\mathcal D_{t_0}=\{(x,t):t\in I_{\max}(x,t_0)\},\qquad
--   \Phi_{t_0}(x,t)=\alpha_{x,t_0}(t),\qquad
--   J_{x,t_0}(t)=d_x\Phi_{t_0}(x,t).$$
--
--   Write $\lambda_x=d\mathcal C_x:X\to\mathbb R$ for the constraint differential.
--
--   For $x=(p,s,a,b,c)$, define
--   $$H(x)=(abc)^{2/3},\quad w(x)=abc(1+4H(x)),\quad
--   \delta(x)=2K-3S,\quad \bar\delta(x)=\frac{2(K+4H(x))}{1+4H(x)},$$
--   $$V(x,t_0,t)=\frac{w(x)\det J_{x,t_0}(t)}{w(\alpha_{x,t_0}(t))}.$$
--   Write $[L]$ for the matrix of a continuous linear operator $L:X\to X$
--   in the standard basis. Set $\Omega(v_0,\ldots,v_4)=\det(v_0,\ldots,v_4)$,
--   $$\omega_x(v_0,\ldots,v_3)=\frac{\Omega(x/2,v_0,\ldots,v_3)}{w(x)},\qquad
--   \varphi_x(v_0,v_1,v_2)=\omega_x(F(x),v_0,v_1,v_2).$$
--
--   A normalized symmetry is a continuous linear equivalence $L:X\to X$ satisfying
--   $$\mathcal C(Lx)=\mathcal C(x),\quad Lx\in W\ \Longleftrightarrow\ x\in W,
--   \quad F(Lx)=LF(x),\quad w(Lx)=w(x),\quad\det L=1.$$
--   These symmetries include the identity, composition, inverse, and the two maps
--   $$R(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a),\qquad
--   S_0(p,s,a,b,c)=(p,-s,a,c,b).$$
--   Transforming a solution replaces its curve $\alpha$ by $L\alpha$ and
--   keeps its time domain.
--
--   Write $\Phi^s_t(x)=\alpha_{x,s}(t)$, with domain $I(x,s)$, and
--   $\mathcal X=\{x:\mathcal C(x)=1,\ N_i(x)>0\ (i=1,2,3)\}$.
--   For $y=(v,l,r)\in\mathbb R^3$ and a wall height $h$, put
--   $$b=e^{-l},\quad c=e^{-r},\quad d=1-v^2-K(h,b,c),\quad
--   U_h=\{y:d>0\},\quad c_h(y)=(-\sqrt d,v,h,b,c).$$
--   For a normalized axis symmetry $A$, the chart is $c_{A,h}=A^{-1}c_h$,
--   with coordinates $\pi_A(x)=((Ax)_1,-\log (Ax)_3,-\log (Ax)_4)$.
--   At $p=-\sqrt d$ its flux density and measure are
--   $$\rho_h(y)=\frac{p^2+v^2-2p}{2|p|(1+4(hbc)^{2/3})},
--   \qquad d\mu_h={\bf1}_{U_h}\rho_h^+\,dy.$$
--   Write $\varphi$ for the signed section flux and $\bar\delta$ for the
--   corrected divergence. The three primary frames interchange axis zero
--   with the chosen dominant axis.
--
--   Let $\mathcal T$ be the union, over primary frames, of the subspaces
--   where the transverse shear and the difference of the other two walls
--   both vanish. Set $\Delta_{ij}(x)=2\sqrt{|N_i(x)N_j(x)|}$.
--   The Brehm attractor input used here is the following proposition:
--   for each $x\in\mathcal X\setminus\mathcal T$ and $i\ne j$,
--   $$\Delta_{ij}(\Phi^0_t(x))\longrightarrow0\qquad(t\to+\infty).$$
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   Define the core radius, angle, and clock factor by
--   $$r(m,v)=\sqrt{(m-1)^2+v^2},\qquad
--   \theta(m,v)=\operatorname{arsinh}\frac{1-m}{v},\qquad
--   d(r,u,w)=1-\frac{(u-w)^2}{r^2}.$$
--   For $y=(m,u,v,w)$, write $r_y=r(m,v)$, $\theta_y=\theta(m,v)$,
--   and $d_y=d(r_y,u,w)$. All quotients use the total convention $x/0=0$.
--
--   The core state space is $\mathbb R^3$ with coordinates $Y=(r,u,p)$.
--   Define
--   $$\eta(m,u,v,w)=(r(m,v),u,vw),\qquad
--   \iota_z(r,u,p)=\left(1-r\tanh z,u,\frac r{\cosh z},
--   \frac p{r/\cosh z}\right).$$
--   For fixed $(z,Y)$ put $v=r/\cosh z$, $w=p/v$, $d=d(r,u,w)$, and define
--   $$\mathcal V(z,Y)=\left(
--   \frac{-\kappa(u,v,w)-\tanh z\,(u-w)^2/r}{d},\quad
--   \frac{u[-r/2+\tanh z+w/\cosh z+(u^2-w^2)/(2r)]}{d},\quad
--   \frac{-2p(1+\kappa(u,v,w))}{rd}\right).$$
--
--   For real $k$, put $\varepsilon_k=1/(10000k)$ and define
--   $$\mathcal K_k=\{(m,u,v,w): |E(m,v)-k^2|\leq1/8,\quad v\geq1,
--   \quad0\leq u\leq\varepsilon_k,\quad0\leq vw\leq\varepsilon_k\}.$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Write $G(y)=6F(y)/D(y)$, $\lambda(y)=6r_yd_y/D(y)$, and
--   $S_k(R,U,P)=(R,kU,P)$. Define
--   $$\mathcal P_y\xi=d\eta_y\xi-d\theta_y\xi\,\mathcal V(\theta_y,\eta(y)),
--   \qquad \mathcal W_{y,t_0,w}(t)=
--   \mathcal P_{\Psi_{t_0}(y,t)}(\mathcal J_{y,t_0}(t)w).$$
--   The entrance parametrization and radial exit factor are
--   $$e(k,u,w)=(1+\sqrt{k^2-1},u,1,w),$$
--   $$f_y=\mathcal V(\theta_y,\eta(y))_0,\qquad c_y=-\tanh\theta_y,
--   \qquad h_y=c_y+f_y/r_y,\qquad \rho_y=c_y/h_y.$$
--   For projective initial data $y$, put
--   $$A_{y,t_0}(t)=1+(\alpha_{\Xi(y),t_0}(t))_0.$$
--   Coordinates of three-vectors are indexed by $0,1,2$; projective
--   coordinates are indexed by $m,u,v,w$.
--
--   For $Y\in\mathbb R^3$, put $x_Y=\Xi(e(Y))$,
--   $\beta_Y(t)=\Psi_0(e(Y),t)$, and
--   $$H_Y=\{t>0:t\in I_{\max}(x_Y,0),\ (\beta_Y(t))_v=1\},
--   \qquad T(Y)=\inf H_Y,\qquad F(Y)=\eta(\beta_Y(T(Y))).$$
--   The infimum uses the total real-order convention. Write $\operatorname{Valid}(Y)$
--   when $T(Y)$ is the least element of $H_Y$, every $t\in[0,T(Y)]$ lies in
--   $I_{\max}(x_Y,0)$ with $A_{e(Y),0}(t)>0$, the active wall is strictly
--   above one for $0<t<T(Y)$, and
--   $$dg_{\alpha_{x_Y,0}(T(Y))}N(\alpha_{x_Y,0}(T(Y)))<0,
--   \qquad g(x)=(\Pi(x))_v.$$
--   All vector and operator norms below use the finite-product supremum norm.
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   Put $c=u(v+w-u)$, $s(m,u,v,w)=m-1-c$,
--   $b(m,u,v,w)=(1-m^2-(v-w)^2+u^2)/2$,
--   $D(m,u,v,w)=3+m^2+K(u,v,w)$, and $r(m,v)=\sqrt{(m-1)^2+v^2}$.
--
--   Define
--   $$\mathcal C_\mu=\{(m,u,v,w):|-m-\mu|\leq1/2,
--   \ 0\leq u\leq1/10000,\ 0\leq v,w\leq1\},$$
--   $$\omega_-(y)=s(-y_m,y_u,y_v,y_w),\qquad H(y)=F(y)/\omega_-(y).$$
--   For a normalized trajectory write
--   $$\beta(t)=\Pi(\alpha_{x,t_0}(t)),\quad A(t)=1+(\alpha_{x,t_0}(t))_0,
--   \quad I=I_{\max}(x,t_0).$$
--
--   For $p=(\mu,u,w)\in\mathbb R^3$, set $e(p)=(-\mu,u,1,w)$,
--   $x_p=\Xi(e(p))$, and
--   $$T_-(p)=\inf\{t>0:t\in I_{\max}(x_p,0),\ (\Psi_0(e(p),t))_w=1\},
--   \qquad P_-(p)=\Psi_0(e(p),T_-(p)).$$
--   Let $V_-(p)$ mean that this infimum is a least element, the full interval
--   $[0,T_-(p)]$ lies in the maximal domain with positive $A$, the growing wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive at the endpoint. The infimum has its total real-order meaning.
--
--   Write $e_+(R,u,w)=(1+\sqrt{R^2-1},u,1,w)$,
--   $e_-(R,u,w)=(1-\sqrt{R^2-1},u,1,w)$,
--   $p_-(R,u,w)=(\sqrt{R^2-1}-1,u,w)$, and
--   $\mathcal R(m,u,v,w)=(-m,u,w,v)$.
--   The physical connection coordinates are
--   $$\mathscr C(p)=\left(\sqrt{(-P_-(p)_0-1)^2+1},P_-(p)_1,P_-(p)_2\right).$$
--   Below $T$ denotes the canonical core return time from $e_+$ and
--   $F(Y)=\eta(\Psi_0(e_+(Y),T(Y)))$ its radial and wall coordinates.
--   Let $\mathscr R(Y)=\mathscr C(p_-(Y))$, $t_r(Y)=T_-(p_-(Y))$,
--   $G=\mathscr R\circ F$, and $t_G(Y)=T(Y)+t_r(F(Y))$.
--   A cone direction at $Y$ has $d_0=1$,
--   $|d_1|\leq\sqrt{Y_1}$, $|d_2|\leq\sqrt{Y_2}$.
--   For a map $H$ with positive output walls, its positive cone property means
--   $dH(Y)d$ has positive radial component and
--   $|(dH(Y)d)_i|\leq\sqrt{H(Y)_i}(dH(Y)d)_0$ for $i=1,2$.
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   For $x=(p,s,a,b,c)$, put
--   $$\psi(p,z)=\frac{\sqrt3\,z}{1+p},\qquad
--   \Pi(x)=(\psi(p,s),\psi(p,a),\psi(p,b),\psi(p,c)).$$
--   For $y=(m,u,v,w)$, set $D(y)=3+m^2+K(u,v,w)$ and
--   $$\Xi_A(y)=\left(A-1,\frac{Am}{\sqrt3},\frac{Au}{\sqrt3},
--   \frac{Av}{\sqrt3},\frac{Aw}{\sqrt3}\right),\qquad
--   \Xi(y)=\Xi_{6/D(y)}(y).$$
--   Write $N(x)=(P,Q,r_1a,r_2b,r_3c)$ for the normalized vector field
--   and $\mathcal C(x)=C(p,s,a,b,c)$ for its constraint.
--
--   The normalized and projective state spaces are $\mathbb R^5$ and $\mathbb R^4$
--   with their finite-product norms. The maps $\Pi,\Xi,D,F$ act on these state spaces.
--
--   The projective vector field in normalized time is
--   $$G(y)=\frac6{D(y)}F(y).$$
--
--   Write $X=\mathbb R^5$, $Y=\mathbb R^4$, and let $\alpha_{x,t_0}$ be the
--   maximal solution of $\alpha'=N(\alpha)$ with initial value $x$ at $t_0$
--   and domain $I_{\max}(x,t_0)$. Put
--   $$J_{x,t_0}(t)=d_x\alpha_{x,t_0}(t),\qquad
--   \Psi_{t_0}(y,t)=\Pi(\alpha_{\Xi(y),t_0}(t)),$$
--   $$\mathcal J_{y,t_0}(t)=d\Pi_{\alpha_{\Xi(y),t_0}(t)}
--   \circ J_{\Xi(y),t_0}(t)\circ d\Xi_y.$$
--
--   For $Y=(k,u,w)\in\mathbb R^3$, define
--   $$e_-(Y)=(1-\sqrt{k^2-1},u,1,w),\quad x_Y=\Xi(e_-(Y)),\quad
--   \beta_Y(t)=\Psi_0(e_-(Y),t),\quad g(x)=(\Pi(x))_v.$$
--   For any real height $\eta$, put
--   $$H_{\eta,Y}=\{t>0:t\in I_{\max}(x_Y,0),\ g(\alpha_{x_Y,0}(t))=\eta\},$$
--   $$T_\eta(Y)=\inf H_{\eta,Y},\qquad P_\eta(Y)=\beta_Y(T_\eta(Y)).$$
--   The infimum uses the total real-order convention. Let
--   $\operatorname{TailValid}_\eta(Y)$ mean that $T_\eta(Y)$ is the least
--   element of $H_{\eta,Y}$, and, writing $T=T_\eta(Y)$, that
--   $$t\in I_{\max}(x_Y,0),\quad 1+(\alpha_{x_Y,0}(t))_0>0
--   \quad(0\leq t\leq T),$$
--   $$g(\alpha_{x_Y,0}(t))>\eta\quad(0\leq t<T),$$
--   $$dg_{\alpha_{x_Y,0}(t)}N(\alpha_{x_Y,0}(t))<0,\quad
--   |(\Pi(\alpha_{x_Y,0}(t)))_w|<1/2\quad(0\leq t\leq T).$$
--   All vector and operator norms use the finite-product supremum norms.
--
--   For $y\in\mathbb R^4$, put $x_y=\Xi(y)$,
--   $$T_+(y)=\inf\{t>0:t\in I_{\max}(x_y,0),\ (\Psi_0(y,t))_v=1\},
--   \qquad P_+(y)=\Psi_0(y,T_+(y)).$$
--   Let $V_+(y)$ mean that this infimum is a least element, the full interval
--   $[0,T_+(y)]$ lies in the maximal domain with
--   $1+(\alpha_{x_y,0}(t))_0>0$, the active wall
--   is below one before the endpoint, and its normalized-time derivative is
--   strictly positive throughout the interval. The infimum has its total
--   real-order meaning.
--
--   For $y=(m,u,v,w)$ define the cyclic chart by
--   $$H(y)=(m+1)^2+K(u,v,w),\qquad
--   \mathcal A(y)=(1-4(m+1)/H,4v/H,4w/H,4u/H).$$
--   Its normalized symmetry is
--   $$A(p,s,a,b,c)=((-p+\sqrt3s)/2,(-\sqrt3p-s)/2,b,c,a).$$
--   Put $z_h(Y)=\mathcal A(P_h(Y))$ and
--   $$\mathcal T(h,Y)=T_h(Y)+T_+(z_h(Y)),\qquad
--   \mathcal P(h,Y)=P_+(z_h(Y)),\qquad x_Y^c=A\Xi(e_-(Y)).$$
--   Write $r(m,v)=\sqrt{(m-1)^2+v^2}$ and $g_*(x)=(\Pi(x))_v$.
--
--   In the era formulas below, $F$ denotes the core return map and
--   $G=\mathscr R\circ F$ its composition with reflection.
--   For $Z=(R,u,w)$ use the natural height $h_*(Z)=\eta((R-2)/2)^J$ and define
--   $S_*(Z)=\mathcal P(h_*(Z),Z)$,
--   $R_*(Z)=r(S_*(Z)_0,S_*(Z)_2)$,
--   $Q_*(Z)=2/R_*(Z)$ and $t_*(Z)=\mathcal T(h_*(Z),Z)$.
--   The complete era maps are
--   $$Z_m=F\circ G^m,\qquad S_m=S_*\circ Z_m,\qquad
--   R_m=R_*\circ Z_m,\qquad P_m=2/R_m.$$
--   For a graph $\Gamma=(U,W)$ write $\Gamma[r]=(r,U(r),W(r))$,
--   $\phi_m(r)=P_m(\Gamma[r])$, $k_m(r)=R_m(\Gamma[r])$,
--   $u_m(r)=S_m(\Gamma[r])_1$, $w_m(r)=S_m(\Gamma[r])_3$.
--   Let $\operatorname{Inv}_{a,b}(f)$ denote Lean's total choice inverse
--   $\operatorname{invFunOn}f\,[a,b]$. For
--   $a=2(m+1+\beta)$, $b=2(m+2-\beta)$, define
--   $$g_m=\operatorname{Inv}_{a,b}(\phi_m),\qquad h_m(y)=2/g_m(y).$$
--   Write $\gamma_n(y)=1/(n+y)$ for the Gauss inverse branch.
--   The retained phase set is
--   $\mathcal H_N=\bigcup_{m<N}(h_m(1-2\beta),h_m(2\beta))$.
--
--   Write $x(Y)=\Xi(e_+(Y))$, $\Phi^s_t(x)=\alpha_{x,s}(t)$ and $I(x,s)$
--   for its maximal domain. Set $Y_j=G^jX$, $Z=F(Y_m)$,
--   $N_m(X)=(R_m(X),S_m(X)_1,S_m(X)_3)$, and
--   $$d_m(X)=\sum_{j<m}t_G(Y_j)+T(Y_m)+t_*(Z).$$
--   The six axis frames realize all permutations of the normalized walls
--   and diagonal shears. Write $L_m$ for the frame obtained by $m$ swaps
--   followed by the cyclic permutation.
--   The event itinerary $\mathcal I_m(X)$ has the following meaning.
--   For $j\le m$, the radius of $Y_j$ exceeds two, the entry is an upward
--   unit-wall crossing, its core first return is valid, and its endpoint
--   is $e_-(F(Y_j))$. For $j<m$ the exit radius exceeds four, and the
--   first positive unit-wall hit in the swapped chart reaches $e_+(Y_{j+1})$,
--   the reflection of the endpoint at time $t_G(Y_j)$. The final exit has
--   radius strictly between two and four. In the cycled exit chart its
--   first positive unit-wall hit occurs at $t_*(Z)$, has state $S_*(Z)$
--   and positive event rate. Finally $\lfloor X_0/2\rfloor=m+1$.
--
--   These data include the positive constraint phase space, the Euclidean
--   distances to the three Taub points, their invariant subspaces, and the
--   pairwise wall products. In the primary frame the squared transverse
--   radius is $s^2+(b-c)^2$; its weighted form multiplies this by $e^{-8a}$.
--   Orbit saturation is the union of the existing flow images at all times.
--   The frame changes, wall charts, actual arrival branches and core flight
--   times specify the events of each finite era.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/tree/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX

import Definitions.Def_BianchiIX_Algebra_Flow
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Definitions.Def_BianchiIX_Algebra_Flux
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.MonotoneConvergence
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_TerminalConeData
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.Floor
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.ByContra
import Mathlib.Topology.Order.Lattice

section

noncomputable section

namespace BianchiIX

def taubRadiusSq (s b c : ℝ) : ℝ := s ^ 2 + (b - c) ^ 2

def taubRadiusHalfRate (p s n b c : ℝ) : ℝ :=
  s * shearMinus s n b c + (b - c) * (rateTwo p s * b - rateThree p s * c)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX









def sectionFluxDensity (p s : ℝ) : ℝ := (shearSq p s - 2 * p) / (2 * |p|)

def correctedSectionFluxDensity (p s a b c : ℝ) : ℝ :=
  sectionFluxDensity p s / (1 + 4 * wallAmplitude a b c)







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def normalizedTaubRadiusSq (x : NormalizedState) : ℝ := taubRadiusSq (x 1) (x 3) (x 4)

def weightedTaubRadiusSq (x : NormalizedState) : ℝ :=
  normalizedTaubRadiusSq x * Real.exp (-8 * x 2)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

abbrev SectionCoordinates := Fin 3 → ℝ

def mainWallRadicand (h : ℝ) (y : SectionCoordinates) : ℝ :=
  1 - y 0 ^ 2 - curvature h (Real.exp (-y 1)) (Real.exp (-y 2))

def mainWallChartDomain (h : ℝ) : Set SectionCoordinates := {y | 0 < mainWallRadicand h y}

def mainWallChart (h : ℝ) (y : SectionCoordinates) : NormalizedState :=
  ![-Real.sqrt (mainWallRadicand h y), y 0, h, Real.exp (-y 1), Real.exp (-y 2)]

def mainWallCoordinates (x : NormalizedState) : SectionCoordinates :=
  ![x 1, -Real.log (x 3), -Real.log (x 4)]





















def mainWallChartDifferential (h : ℝ) (y : SectionCoordinates) : SectionCoordinates →L[ℝ] NormalizedState :=
  fderiv ℝ (mainWallChart h) y







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def normalizedOrbitSaturation (S : Set NormalizedState) : Set NormalizedState :=
  {x | ∃ z ∈ S, ∃ t ∈ normalizedMaxDomain z 0, normalizedMaxCurve z 0 t = x}









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX





def mainWallChartFrame (h : ℝ) (y : SectionCoordinates) : Fin 3 → NormalizedState :=
  fun i => mainWallChartDifferential h y (Pi.single i 1)

def mainWallChartDensity (h : ℝ) (y : SectionCoordinates) : ℝ :=
  correctedSectionFluxDensity (mainWallChart h y 0) (y 0) h (Real.exp (-y 1)) (Real.exp (-y 2))











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

def normalizedShears (x : NormalizedState) : Fin 3 → ℝ :=
  ![-2 * x 0, x 0 - Real.sqrt 3 * x 1, x 0 + Real.sqrt 3 * x 1]

def normalizedWalls (x : NormalizedState) : Fin 3 → ℝ := ![x 2, x 3, x 4]





open NormalizedSymmetry in
def axisFrame (i : Fin 6) : NormalizedSymmetry :=
  ![refl, cycle, cycle.trans cycle, swap, cycle.trans swap, (cycle.trans cycle).trans swap] i

def axisOrder (i : Fin 6) : Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1], ![0, 2, 1], ![1, 0, 2], ![2, 1, 0]] i



theorem axisOrder_covers : ∀ σ : Equiv.Perm (Fin 3), ∃ i, ∀ j, axisOrder i j = σ j := by decide







/-- Each permutation acts on walls and diagonal shear by exactly the same permutation. -/
def axisPermutation (σ : Equiv.Perm (Fin 3)) : NormalizedSymmetry :=
  axisFrame (axisOrder_covers σ).choose











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def axisWallChart (A : NormalizedSymmetry) (h : ℝ) (y : SectionCoordinates) : NormalizedState :=
  A.map.symm (mainWallChart h y)

def axisWallCoordinates (A : NormalizedSymmetry) (x : NormalizedState) : SectionCoordinates :=
  mainWallCoordinates (A.map x)















def axisWallChartDifferential (A : NormalizedSymmetry) (h : ℝ) (y : SectionCoordinates) :
    SectionCoordinates →L[ℝ] NormalizedState := fderiv ℝ (axisWallChart A h) y







def axisWallChartFrame (A : NormalizedSymmetry) (h : ℝ) (y : SectionCoordinates) : Fin 3 → NormalizedState :=
  fun i => axisWallChartDifferential A h y (Pi.single i 1)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

def axisSectionTimes (A : NormalizedSymmetry) (h ε : ℝ) (x : NormalizedState) (t₀ T : ℝ) : Set ℝ :=
  {t ∈ Icc t₀ T | A.map (normalizedMaxCurve x t₀ t) 2 = h ∧
    A.map (normalizedMaxCurve x t₀ t) 0 ≤ -ε}





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def axisWallFlowDomain (A : NormalizedSymmetry) (h : ℝ) : Set (SectionCoordinates × ℝ) :=
  {p | p.1 ∈ mainWallChartDomain h ∧ p.2 ∈ normalizedMaxDomain (axisWallChart A h p.1) 0}

def axisWallFlowMap (A : NormalizedSymmetry) (h : ℝ) (p : SectionCoordinates × ℝ) : NormalizedState :=
  normalizedMaxCurve (axisWallChart A h p.1) 0 p.2







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- An injective local arrival of the exact flow between two independently chosen axis charts. -/
structure AxisWallArrival (A B : NormalizedSymmetry) (h k t₀ : ℝ) where
  source : Set SectionCoordinates
  time : NormalizedState → ℝ
  map : SectionCoordinates → SectionCoordinates
  isOpen_source : IsOpen source
  source_chart : source ⊆ mainWallChartDomain h
  target_chart : MapsTo map source (mainWallChartDomain k)
  time_mem : ∀ y ∈ source, time (axisWallChart A h y) ∈ normalizedMaxDomain (axisWallChart A h y) t₀
  time_regular : ∀ y ∈ source, ContDiffAt ℝ 1 time (axisWallChart A h y)
  map_regular : ∀ y ∈ source, ContDiffAt ℝ 1 map y
  arrival : ∀ y ∈ source,
    axisWallChart B k (map y) = normalizedMaxCurve (axisWallChart A h y) t₀ (time (axisWallChart A h y))
  injOn : InjOn map source



namespace AxisWallArrival

variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)



def jacobian (y : SectionCoordinates) : ℝ :=
  mainWallChartDensity k (P.map y) * |(fderiv ℝ P.map y).det| / mainWallChartDensity h y











end AxisWallArrival



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def axisWallArrivalRelation (A B : NormalizedSymmetry) (h k t₀ : ℝ) : Set (SectionCoordinates × ℝ) :=
  {z | z.1 ∈ mainWallChartDomain h ∧ z.2 ∈ normalizedMaxDomain (axisWallChart A h z.1) t₀ ∧
    B.map (normalizedMaxCurve (axisWallChart A h z.1) t₀ z.2) 2 = k ∧
    B.map (normalizedMaxCurve (axisWallChart A h z.1) t₀ z.2) 0 < 0}

def AxisWallArrival.empty (A B : NormalizedSymmetry) (h k t₀ : ℝ) : AxisWallArrival A B h k t₀ where
  source := ∅
  time := fun _ => t₀
  map := id
  isOpen_source := isOpen_empty
  source_chart := empty_subset _
  target_chart := fun _ hy => hy.elim
  time_mem := fun _ hy => hy.elim
  time_regular := fun _ hy => hy.elim
  map_regular := fun _ hy => hy.elim
  arrival := fun _ hy => hy.elim
  injOn := injOn_empty _

/-- The countable branches cover the actual crossing relation, including every admissible time. -/
structure AxisWallArrivalAtlas (A B : NormalizedSymmetry) (h k t₀ : ℝ) where
  branch : ℕ → AxisWallArrival A B h k t₀
  covers : ∀ z ∈ axisWallArrivalRelation A B h k t₀,
    ∃ n, z.1 ∈ (branch n).source ∧ (branch n).time (axisWallChart A h z.1) = z.2



namespace AxisWallArrival

variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

def coordinateTime (y : SectionCoordinates) : ℝ := P.time (axisWallChart A h y)







end AxisWallArrival



abbrev AxisWallAtlasFamily {ι : Type*} (A : NormalizedSymmetry) (B : ι → NormalizedSymmetry)
    (h : ℝ) (k : ι → ℝ) (t₀ : ℝ) := ∀ i, AxisWallArrivalAtlas A (B i) h (k i) t₀



end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def axisFamilyChart {ι : Type*} (B : ι → NormalizedSymmetry) (k : ι → ℝ)
    (z : ι × SectionCoordinates) : NormalizedState := axisWallChart (B z.1) (k z.1) z.2

def axisFamilySection {ι : Type*} (E : ι → Set SectionCoordinates) : Set (ι × SectionCoordinates) :=
  {z | z.2 ∈ E z.1}



def dominantWallChartDomain (h : ℝ) : Set SectionCoordinates :=
  {y | y ∈ mainWallChartDomain h ∧ Real.exp (-y 1) < h ∧ Real.exp (-y 2) < h}









/-- One verified frame for each possible dominant physical axis. -/
def primaryAxisFrame (i : Fin 3) : NormalizedSymmetry := axisPermutation (Equiv.swap 0 i)









end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

/-- The physical Euclidean distance, distinct from the sup norm on `NormalizedState`. -/
def normalizedEuclideanDistance (x y : NormalizedState) : ℝ :=
  dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 5)) (WithLp.toLp 2 y)

def taubPoint (i : Fin 3) : NormalizedState :=
  ![![-1, 0, 0, 0, 0], ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0],
    ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]] i





























end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def physicalPhaseSpace : Set NormalizedState :=
  {x | positiveWalls x ∧ stateConstraint x = 1}







def taubSubspaces : Set NormalizedState :=
  {x | ∃ i : Fin 3, normalizedTaubRadiusSq ((primaryAxisFrame i).map x) = 0}







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

/-- The entire forward exact orbit stays at least `ε` from all three Taub points. -/
def normalizedTaubAvoidance (ε : ℝ) (x : NormalizedState) : Prop :=
  ∀ t, 0 ≤ t → t ∈ normalizedMaxDomain x 0 →
    ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)











end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def normalizedWallProduct (x : NormalizedState) : ℝ := x 2 * x 3 * x 4







end BianchiIX

end
end

section

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_shears (x : NormalizedState) :
    normalizedShears (axisCycle x) = ![normalizedShears x 1, normalizedShears x 2, normalizedShears x 0] := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisCycle] <;> ring_nf <;> norm_num [hs] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_shears (x : NormalizedState) :
    normalizedShears (axisSwap x) = ![normalizedShears x 0, normalizedShears x 2, normalizedShears x 1] := by
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisSwap] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisOrder_bijective : ∀ i, Function.Bijective (axisOrder i) := by decide

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_apply (i : Fin 6) (x : NormalizedState) :
    (axisFrame i).map x =
      ![x, axisCycle x, axisCycle (axisCycle x), axisSwap x,
        axisSwap (axisCycle x), axisSwap (axisCycle (axisCycle x))] i := by
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_walls (i : Fin 6) (x : NormalizedState) :
    normalizedWalls ((axisFrame i).map x) = fun j => normalizedWalls x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_shears (i : Fin 6) (x : NormalizedState) :
    normalizedShears ((axisFrame i).map x) = fun j => normalizedShears x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i
  · ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle x) = _
    rw [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle (axisCycle x)) = _
    simp only [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap x) = _
    rw [axisSwap_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle x)) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle (axisCycle x))) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedState_ext_shears_walls {x y : NormalizedState}
    (hs : normalizedShears x = normalizedShears y) (hw : normalizedWalls x = normalizedWalls y) : x = y := by
  have h₀ := congrFun hs 0
  have h₁ := congrFun hs 1
  change -2 * x 0 = -2 * y 0 at h₀
  change x 0 - Real.sqrt 3 * x 1 = y 0 - Real.sqrt 3 * y 1 at h₁
  have hx₀ : x 0 = y 0 := by linarith
  have hx₁ : x 1 = y 1 := mul_left_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    (by linarith : Real.sqrt 3 * x 1 = Real.sqrt 3 * y 1)
  ext i
  fin_cases i
  · exact hx₀
  · exact hx₁
  · exact congrFun hw 0
  · exact congrFun hw 1
  · exact congrFun hw 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_comp (i j : Fin 6) :
    ∃ k : Fin 6, ∀ x : NormalizedState,
      (axisFrame i).map ((axisFrame j).map x) = (axisFrame k).map x := by
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective (axisOrder i) (axisOrder_bijective i)
  let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective (axisOrder j) (axisOrder_bijective j)
  obtain ⟨k, hk⟩ := axisOrder_covers (σ.trans τ)
  refine ⟨k, fun x => normalizedState_ext_shears_walls ?_ ?_⟩
  · ext l
    simp only [axisFrame_shears, hk]
    rfl
  · ext l
    simp only [axisFrame_walls, hk]
    rfl

end
end


noncomputable section

namespace BianchiIX

/-- Original time spent in the first `m` nonterminal core-reflection passages. -/
def corePrefixTime (m : ℕ) (X : CoreAngleState) : ℝ :=
  ∑ j ∈ Finset.range m, coreReflectionTime ((coreReflectionState coreRadiusReturnTime)^[j] X)

def corePrefixFrame : ℕ → Fin 6
  | 0 => 0
  | m + 1 => (axisFrame_comp 3 (corePrefixFrame m)).choose







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

/-- The full original time includes every reflection, the last downward core, and the terminal connection. -/
def eraReturnTime (η : ℝ) (J m : ℕ) (X : CoreAngleState) : ℝ :=
  terminalNaturalTime η J (eraCoreExit m X) +
    (coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X) + corePrefixTime m X)

def eraReturnFrame (m : ℕ) : Fin 6 := (axisFrame_comp 1 (corePrefixFrame m)).choose





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set

/-- A finite block of actual first core returns, followed by its first terminal connection. -/
structure EraEventItinerary (η : ℝ) (J m : ℕ) (X : CoreAngleState) : Prop where
  core : ∀ j ≤ m,
    let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
    2 < Y 0 ∧
      (projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) = 1 ∧
        0 < normalizedEventRate projectiveActiveWall (fromProjectiveState (coreRadiusEntry Y)) 0 0) ∧
      coreRadiusReturnValid Y ∧
      coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
        projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y)
  reflection : ∀ j < m,
    let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
    let Z := coreReturnState coreRadiusReturnTime Y
    let x := axisSwap (fromProjectiveState (coreTailEntry Z))
    4 < Z 0 ∧
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
        projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} (reflectionReturnTime Z) ∧
      toProjectiveState (normalizedMaxCurve x 0 (reflectionReturnTime Z)) =
        coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j + 1] X) ∧
      coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j + 1] X) =
        projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))
  terminal :
    let Z := eraCoreExit m X
    let x := axisCycle (fromProjectiveState (coreTailEntry Z))
    let T := terminalNaturalTime η J Z
    (2 < Z 0 ∧ Z 0 < 4) ∧
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
        projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
      toProjectiveState (normalizedMaxCurve x 0 T) = terminalNaturalState η J Z ∧
      terminalNaturalState η J Z 2 = 1 ∧
      0 < normalizedEventRate projectiveActiveWall x 0 T
  count : Nat.floor (X 0 / 2) = m + 1







end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def WallProductDecay (x : NormalizedState) : Prop :=
  ∀ i j : Fin 3, i ≠ j → Tendsto
    (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t))
      atTop (𝓝 0)





end BianchiIX

end
end

section

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Brehm's delta for the complementary wall pair. -/
def brehmPairDelta (x : NormalizedState) (i j : Fin 3) : ℝ :=
  2 * Real.sqrt |wallValue i x * wallValue j x|



/-- The delta-decay consequence of Brehm's Section 6 local and Bianchi IX global
attractor theorems (2016, arXiv:1606.08058). The source uses the same coordinates
and singularity-directed time as `normalizedField`; see its unpacked
Wainwright-Hsu equations and the definitions of the Taub spaces in Section 2.
For positive walls, the excluded spaces are exactly `taubSubspaces`.
This proposition is an explicit literature parameter, not a project axiom.
It asserts no era coding, statistical conclusion, or transverse nullity. -/
def Literature.BrehmIXAttractorInput : Prop :=
  ∀ x : NormalizedState, x ∈ physicalPhaseSpace → x ∉ taubSubspaces →
    ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => brehmPairDelta (normalizedMaxCurve x 0 t) i j) atTop (𝓝 0)



end BianchiIX

end
end


